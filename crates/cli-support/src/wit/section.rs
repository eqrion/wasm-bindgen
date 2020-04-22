//! Support for generating a standard wasm interface types
//!
//! This module has all the necessary support for generating a full-fledged
//! standard wasm interface types section as defined by the `wit_walrus`
//! crate. This module also critically assumes that the WebAssembly module
//! being generated **must be standalone**. In this mode all sorts of features
//! supported by `#[wasm_bindgen]` aren't actually supported, such as closures,
//! imports of global js names, js getters/setters, exporting structs, etc.
//! These features may all eventually come to the standard bindings proposal,
//! but it will likely take some time. In the meantime this module simply focuses
//! on taking what's already a valid wasm module and letting it through with a
//! standard WebIDL custom section. All other modules generate an error during
//! this binding process.
//!
//! Note that when this function is called and used we're also not actually
//! generating any JS glue. Any JS glue currently generated is also invalid if
//! the module contains the wasm bindings section and it's actually respected.

use crate::wit::InstructionData;
use crate::wit::{Adapter, AdapterId, AdapterJsImportKind, AdapterType, Instruction};
use crate::wit::{AdapterKind, NonstandardWitSection, WasmBindgenAux};
use crate::wit::{AuxImport, AuxValue, JsImport, JsImportName};
use anyhow::{anyhow, bail, Error};
use std::collections::{HashMap, HashSet};
use walrus::Module;
use wit_walrus::Instruction as WitInstruction;

pub fn add(module: &mut Module) -> Result<(), Error> {
    let nonstandard = module
        .customs
        .delete_typed::<NonstandardWitSection>()
        .unwrap();
    let mut aux = module.customs.delete_typed::<WasmBindgenAux>().unwrap();
    let mut section = wit_walrus::WasmInterfaceTypes::default();

    let mut valid_adapters = HashSet::new();
    for (id, func) in crate::sorted_iter(&nonstandard.adapters) {
        let mut referenced_adapters = Vec::new();

        match &func.kind {
            AdapterKind::Import { .. } => continue,
            AdapterKind::Local { instructions } => {
                for instr in instructions {
                    use Instruction::*;
                    match &instr.instr {
                        Standard(s) => match s {
                            WitInstruction::CallAdapter(_) => unimplemented!(),
                            _ => {}
                        },
                        CallAdapter(i) => {
                            referenced_adapters.push((*i, &nonstandard.adapters[i]));
                        }
                        _ => { }
                    }
                }
            }
        }

        let adapter_context = |id: AdapterId| {
            if let Some((name, _)) = nonstandard.exports.iter().find(|p| p.1 == id) {
                return format!("in adapter export `{}`", name);
            }
            if let Some((core, _, _)) = nonstandard.implements.iter().find(|p| p.2 == id) {
                let import = module.imports.get(*core);
                return format!(
                    "in adapter implements for `{}::{}`",
                    import.module, import.name
                );
            }
            if let Some(aux_import) = aux.import_map.get(&id) {
                format!("in adapter import {:?}", aux_import)
            } else {
                format!("in adapter import")
            }
        };

        if referenced_adapters.len() != 1 {
            eprintln!("Skipping local-only adapter.");
            continue;
        }
        referenced_adapters.push((*id, func));
        let mut errors = Vec::new();
        for (id, adapter) in &referenced_adapters {
            if let Err(error) = check_adapter(*id, adapter, module, &aux) {
                errors.push((error, *id, adapter));
            }
        }
        if errors.is_empty() {
            for (id, _) in &referenced_adapters {
                if let Some((import, _, _)) = nonstandard.implements.iter().find(|p| p.2 == *id) {
                    aux.implements_in_standard.insert(*import);
                }
                valid_adapters.insert(*id);
            }
        } else {
            eprintln!("Skipping adapter.");
            for (err, id, func) in errors {
                // eprintln!("\tContext: {:#?}", adapter_context(id));
                eprintln!("\tAdapter: {:?}", func);
                eprintln!("\tError: {:?}", err);
            }
            eprintln!();
        }
    }

    let mut imports_in_standard = HashMap::new();
    let mut adapters_in_standard = HashMap::new();
    for (id, func) in crate::sorted_iter(&nonstandard.adapters) {
        if !valid_adapters.contains(id) {
            continue;
        }

        let params = translate_tys(&func.params).unwrap();
        let results = translate_tys(&func.results).unwrap();
        let ty = section.types.add(params, results);

        let func_id = match &func.kind {
            AdapterKind::Import {
                module,
                name,
                kind: _,
            } => {
                let mut module = module.clone();
                if module == "__wbindgen_placeholder__" {
                    module = "wbg".to_string();
                }

                eprintln!(
                    "Generating interface for adapter import {:?}.{:?}",
                    module, name
                );

                let (func_id, import_id) = section.add_import_func(&module, name, ty);
                imports_in_standard.insert(*id, import_id);
                func_id
            }
            AdapterKind::Local { .. } => {
                eprintln!("Generating interface for adapter local");

                let func_id = section.funcs.add_local(ty, Vec::new());
                func_id
            }
        };
        adapters_in_standard.insert(*id, func_id);
    }

    // Fill in the bodies of local adapters
    for (id, func) in nonstandard.adapters.iter() {
        if !adapters_in_standard.contains_key(id) {
            continue;
        }
        let instructions = match &func.kind {
            AdapterKind::Local { instructions } => instructions,
            AdapterKind::Import { .. } => continue,
        };
        let mut result = match &mut section.funcs.get_mut(adapters_in_standard[id]).kind {
            wit_walrus::FuncKind::Local(i) => i,
            _ => unreachable!(),
        };

        for instruction in instructions {
            translate_instruction(instruction, &mut result, &adapters_in_standard, module).unwrap();
        }
    }

    // Link core imports to adapters
    for (_, core, adapter) in nonstandard.implements.iter() {
        if !adapters_in_standard.contains_key(adapter) {
            continue;
        }
        section.implements.add(adapters_in_standard[adapter], *core);
    }

    for id in adapters_in_standard.keys() {
        aux.adapters_in_standard.insert(*id);
    }
    aux.imports_in_standard = imports_in_standard;

    module.customs.add(*nonstandard);
    module.customs.add(*aux);
    module.customs.add(section);
    Ok(())
}

fn check_adapter(
    id: AdapterId,
    func: &Adapter,
    module: &Module,
    aux: &WasmBindgenAux,
) -> Result<(), Error> {
    if let Some(_) = aux.export_map.get(&id) {
        bail!("exports are unsupported")
    }
    if let Some(import) = aux.import_map.get(&id) {
        check_standard_import(import)?;
    }

    translate_tys(&func.params)?;
    translate_tys(&func.results)?;

    match &func.kind {
        AdapterKind::Import {
            module: _,
            name,
            kind,
        } => {
            if name.contains("taggedvalue") ||
                name.contains("__wbg_debug_") ||
                name.contains("__wbg_error_") ||
                name.contains("__wbg_info_") ||
                name.contains("__wbg_log_") ||
                name.contains("__wbg_warn_") {
                bail!("handcoded skip")
            }
            if *kind == AdapterJsImportKind::Constructor {
                bail!("constructors are unsupported")
            }
        }
        AdapterKind::Local { instructions } => {
            for instruction in instructions {
                check_instruction(&instruction, module, aux)?;
            }
        }
    }
    Ok(())
}

fn check_instruction(
    instr: &InstructionData,
    module: &Module,
    aux: &WasmBindgenAux,
) -> Result<(), Error> {
    use Instruction::*;

    match &instr.instr {
        Standard(_) => { },
        CallAdapter(id) => {
            if let Some(import) = aux.import_map.get(id) {
                match import {
                    AuxImport::Value(value) => {
                        let import = match value {
                            AuxValue::Bare(imp) => imp,
                            AuxValue::Getter(imp, _) => imp,
                            AuxValue::ClassGetter(imp, _) => imp,
                            AuxValue::Setter(imp, _) => imp,
                            AuxValue::ClassSetter(imp, _) => imp,
                        };
                        match &import.name {
                            JsImportName::Global { name } => {
                                if name == "window" || name == "Window" {
                                    bail!("cannot use proxied objects");
                                }
                            }
                            _ => { }
                        }
                    }
                    _ => {}
                }
            }
        }
        CallExport(e) => match module.exports.get(*e).item {
            walrus::ExportItem::Function(_) => {}
            _ => bail!("can only call exported functions"),
        },
        CallTableElement(e) => {
            let table = module
                .tables
                .main_function_table()?
                .ok_or_else(|| anyhow!("no function table found in module"))?;
            let functions = match &module.tables.get(table).kind {
                walrus::TableKind::Function(f) => f,
                _ => unreachable!(),
            };
            match functions.elements.get(*e as usize) {
                Some(Some(_)) => {}
                _ => bail!("expected to find an element of the function table"),
            }
        }
        StringToMemory { .. } => {}
        StoreRetptr {
            ty: AdapterType::I32,
            ..
        } => {}
        StoreRetptr { .. } | LoadRetptr { .. } | Retptr => {
            bail!("return pointers aren't supported in wasm interface types");
        }
        I32FromBool | BoolFromI32 => { }
        I32FromStringFirstChar | StringFromChar => {
            bail!("chars aren't supported in wasm interface types");
        }
        I32FromAnyrefOwned | I32FromAnyrefBorrow | AnyrefLoadOwned | TableGet => {
            bail!("anyref pass failed to sink into wasm module");
        }
        I32FromAnyrefRustOwned { .. } | I32FromAnyrefRustBorrow { .. } | RustFromI32 { .. } => {
            bail!("rust types aren't supported in wasm interface types");
        }
        I32Split64 { .. } | I64FromLoHi { .. } => {
            bail!("64-bit integers aren't supported in wasm-bindgen");
        }
        I32FromOptionAnyref { table_and_alloc } => {
            match table_and_alloc {
                Some(..) => { }
                None => bail!("interface types requires anyref enabled"),
            }
        }
        I32SplitOption64 { .. }
        | I32FromOptionU32Sentinel
        | I32FromOptionRust { .. }
        | I32FromOptionBool
        | I32FromOptionChar
        | I32FromOptionEnum { .. }
        | FromOptionNative { .. }
        | OptionVector { .. }
        | OptionString { .. }
        | OptionRustFromI32 { .. }
        | OptionVectorLoad { .. }
        | OptionView { .. }
        | OptionU32Sentinel
        | ToOptionNative { .. }
        | OptionBoolFromI32
        | OptionCharFromI32
        | OptionEnumFromI32 { .. }
        | Option64FromI32 { .. } => {
            bail!("optional type {:?} isn't supported in wasm bindgen", instr.instr);
        }
        MutableSliceToMemory { .. } | VectorToMemory { .. } | VectorLoad { .. } | View { .. } => {
            bail!("vector slices aren't supported in wasm interface types yet");
        }
        CachedStringLoad { .. } => {
            bail!("cached strings aren't supported in wasm interface types");
        }
        StackClosure { .. } => {
            bail!("closures aren't supported in wasm interface types");
        }
    };
    Ok(())
}

fn translate_instruction(
    instr: &InstructionData,
    results: &mut Vec<wit_walrus::Instruction>,
    adapters_in_standard: &HashMap<AdapterId, wit_walrus::FuncId>,
    module: &Module,
) -> Result<(), Error> {
    use Instruction::*;

    match &instr.instr {
        Standard(s) => { results.push(s.clone()) },
        CallAdapter(id) => {
            let id = adapters_in_standard[id];
            results.push(wit_walrus::Instruction::CallAdapter(id));
        }
        CallExport(e) => match module.exports.get(*e).item {
            walrus::ExportItem::Function(f) => results.push(wit_walrus::Instruction::CallCore(f)),
            _ => bail!("can only call exported functions"),
        },
        CallTableElement(e) => {
            let table = module
                .tables
                .main_function_table()?
                .ok_or_else(|| anyhow!("no function table found in module"))?;
            let functions = match &module.tables.get(table).kind {
                walrus::TableKind::Function(f) => f,
                _ => unreachable!(),
            };
            match functions.elements.get(*e as usize) {
                Some(Some(f)) => results.push(wit_walrus::Instruction::CallCore(*f)),
                _ => bail!("expected to find an element of the function table"),
            }
        }
        StringToMemory {
            mem,
            malloc,
            realloc: _,
        } => results.push(wit_walrus::Instruction::StringToMemory {
            mem: *mem,
            malloc: *malloc,
        }),
        StoreRetptr {
            ty: AdapterType::I32,
            offset,
            mem,
        } => {
            results.push(wit_walrus::Instruction::ArgGet(0));
            results.push(wit_walrus::Instruction::I32Store(wit_walrus::Store {
                offset: *offset as u32,
                mem: *mem,
            }));
        }
        StoreRetptr { .. } | LoadRetptr { .. } | Retptr => {
            bail!("return pointers aren't supported in wasm interface types");
        }
        I32FromBool => {
            results.push(wit_walrus::Instruction::I32FromBool);
        }
        BoolFromI32 => {
            results.push(wit_walrus::Instruction::BoolFromI32);
        }
        I32FromStringFirstChar | StringFromChar => {
            bail!("chars aren't supported in wasm interface types");
        }
        I32FromAnyrefOwned | I32FromAnyrefBorrow | AnyrefLoadOwned | TableGet => {
            bail!("anyref pass failed to sink into wasm module");
        }
        I32FromAnyrefRustOwned { .. } | I32FromAnyrefRustBorrow { .. } | RustFromI32 { .. } => {
            bail!("rust types aren't supported in wasm interface types");
        }
        I32Split64 { .. } | I64FromLoHi { .. } => {
            bail!("64-bit integers aren't supported in wasm-bindgen");
        }
        I32FromOptionAnyref { table_and_alloc } => {
            match table_and_alloc {
                Some((table, alloc)) => {
                    assert!(table.index() == 1);
                    // Anyref (maybe null) on stack
                    // Push an allocated table index in the table
                    results.push(wit_walrus::Instruction::CallCore(*alloc));
                    // Push a 'fake' table.set which operates on reversed
                    // operands and leaves the index on the stack
                    results.push(wit_walrus::Instruction::AnyrefTableTee);
                }
                None => bail!("interface types requires anyref enabled"),
            }
        }
        I32SplitOption64 { .. }
        | I32FromOptionU32Sentinel
        | I32FromOptionRust { .. }
        | I32FromOptionBool
        | I32FromOptionChar
        | I32FromOptionEnum { .. }
        | FromOptionNative { .. }
        | OptionVector { .. }
        | OptionString { .. }
        | OptionRustFromI32 { .. }
        | OptionVectorLoad { .. }
        | OptionView { .. }
        | OptionU32Sentinel
        | ToOptionNative { .. }
        | OptionBoolFromI32
        | OptionCharFromI32
        | OptionEnumFromI32 { .. }
        | Option64FromI32 { .. } => {
            bail!("optional types aren't supported in wasm bindgen");
        }
        MutableSliceToMemory { .. } | VectorToMemory { .. } | VectorLoad { .. } | View { .. } => {
            bail!("vector slices aren't supported in wasm interface types yet");
        }
        CachedStringLoad { .. } => {
            bail!("cached strings aren't supported in wasm interface types");
        }
        StackClosure { .. } => {
            bail!("closures aren't supported in wasm interface types");
        }
    };
    Ok(())
}

fn check_standard_import(import: &AuxImport) -> Result<(), Error> {
    let desc_js = |js: &JsImport| {
        let mut extra = String::new();
        for field in js.fields.iter() {
            extra.push_str(".");
            extra.push_str(field);
        }
        match &js.name {
            JsImportName::Global { name } | JsImportName::VendorPrefixed { name, .. } => {
                format!("global `{}{}`", name, extra)
            }
            JsImportName::Module { module, name } => {
                format!("`{}{}` from '{}'", name, extra, module)
            }
            JsImportName::LocalModule { module, name } => {
                format!("`{}{}` from local module '{}'", name, extra, module)
            }
            JsImportName::InlineJs {
                unique_crate_identifier,
                name,
                ..
            } => format!(
                "`{}{}` from inline js in '{}'",
                name, extra, unique_crate_identifier
            ),
        }
    };

    let item = match import {
        AuxImport::Value(value) => {
            let import = match value {
                AuxValue::Bare(import) => import,
                AuxValue::Getter(import, _) => import,
                AuxValue::ClassGetter(import, _) => import,
                AuxValue::Setter(import, _) => import,
                AuxValue::ClassSetter(import, _) => import,
            };
            if let JsImportName::Global { name } = &import.name {
                if name == "Window" || name == "EventTarget" {
                    bail!("cannot use proxied objects");
                }
            }
            return Ok(());
        }
        AuxImport::ValueWithThis(js, method) => format!("method `{}.{}`", desc_js(js), method),
        AuxImport::Instanceof(js) => format!("instance of check of {}", desc_js(js)),
        AuxImport::Static(js) => format!("static js value {}", desc_js(js)),
        AuxImport::StructuralMethod(name) => format!("structural method `{}`", name),
        AuxImport::StructuralGetter(name)
        | AuxImport::StructuralSetter(name)
        | AuxImport::StructuralClassGetter(_, name)
        | AuxImport::StructuralClassSetter(_, name) => {
            format!("structural field access of `{}`", name)
        }
        AuxImport::IndexingDeleterOfClass(_)
        | AuxImport::IndexingDeleterOfObject
        | AuxImport::IndexingGetterOfClass(_)
        | AuxImport::IndexingGetterOfObject
        | AuxImport::IndexingSetterOfClass(_)
        | AuxImport::IndexingSetterOfObject => format!("indexing getters/setters/deleters"),
        AuxImport::WrapInExportedClass(name) => {
            format!("wrapping a pointer in a `{}` js class wrapper", name)
        }
        AuxImport::Intrinsic(intrinsic) => {
            format!("wasm-bindgen specific intrinsic `{}`", intrinsic.name())
        }
        AuxImport::Closure { .. } => format!("creating a `Closure` wrapper"),
    };
    bail!("import of {} requires JS glue", item);
}

fn translate_tys(tys: &[AdapterType]) -> Result<Vec<wit_walrus::ValType>, Error> {
    tys.iter()
        .map(|ty| {
            ty.to_wit()
                .ok_or_else(|| anyhow!("type {:?} isn't supported in standard interface types", ty))
        })
        .collect()
}
