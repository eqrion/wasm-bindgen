#![allow(unused_imports)]
use super::*;
use wasm_bindgen::prelude::*;
#[cfg(web_sys_unstable_apis)]
#[wasm_bindgen]
extern "C" {
    # [ wasm_bindgen ( extends = :: js_sys :: Object , js_name = GPUBuffer , typescript_type = "GPUBuffer" ) ]
    #[derive(Debug, Clone, PartialEq, Eq)]
    #[doc = "The `GpuBuffer` class."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/GPUBuffer)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `GpuBuffer`*"]
    #[doc = ""]
    #[doc = "*This API is unstable and requires `--cfg=web_sys_unstable_apis` to be activated, as"]
    #[doc = "[described in the `wasm-bindgen` guide](https://rustwasm.github.io/docs/wasm-bindgen/web-sys/unstable-apis.html)*"]
    pub type GpuBuffer;
    #[cfg(web_sys_unstable_apis)]
    # [ wasm_bindgen ( final , method , getter , js_class = "GPUBuffer" , js_name = label ) ]
    #[doc = "Getter for the `label` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/GPUBuffer/label)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `GpuBuffer`*"]
    #[doc = ""]
    #[doc = "*This API is unstable and requires `--cfg=web_sys_unstable_apis` to be activated, as"]
    #[doc = "[described in the `wasm-bindgen` guide](https://rustwasm.github.io/docs/wasm-bindgen/web-sys/unstable-apis.html)*"]
    pub fn label(this: &GpuBuffer) -> Option<String>;
    #[cfg(web_sys_unstable_apis)]
    # [ wasm_bindgen ( final , method , setter , js_class = "GPUBuffer" , js_name = label ) ]
    #[doc = "Setter for the `label` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/GPUBuffer/label)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `GpuBuffer`*"]
    #[doc = ""]
    #[doc = "*This API is unstable and requires `--cfg=web_sys_unstable_apis` to be activated, as"]
    #[doc = "[described in the `wasm-bindgen` guide](https://rustwasm.github.io/docs/wasm-bindgen/web-sys/unstable-apis.html)*"]
    pub fn set_label(this: &GpuBuffer, value: Option<&str>);
    #[cfg(web_sys_unstable_apis)]
    # [ wasm_bindgen ( method , final , js_class = "GPUBuffer" , js_name = destroy ) ]
    #[doc = "The `destroy()` method."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/GPUBuffer/destroy)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `GpuBuffer`*"]
    #[doc = ""]
    #[doc = "*This API is unstable and requires `--cfg=web_sys_unstable_apis` to be activated, as"]
    #[doc = "[described in the `wasm-bindgen` guide](https://rustwasm.github.io/docs/wasm-bindgen/web-sys/unstable-apis.html)*"]
    pub fn destroy(this: &GpuBuffer);
    #[cfg(web_sys_unstable_apis)]
    # [ wasm_bindgen ( method , final , js_class = "GPUBuffer" , js_name = mapReadAsync ) ]
    #[doc = "The `mapReadAsync()` method."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/GPUBuffer/mapReadAsync)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `GpuBuffer`*"]
    #[doc = ""]
    #[doc = "*This API is unstable and requires `--cfg=web_sys_unstable_apis` to be activated, as"]
    #[doc = "[described in the `wasm-bindgen` guide](https://rustwasm.github.io/docs/wasm-bindgen/web-sys/unstable-apis.html)*"]
    pub fn map_read_async(this: &GpuBuffer) -> ::js_sys::Promise;
    #[cfg(web_sys_unstable_apis)]
    # [ wasm_bindgen ( method , final , js_class = "GPUBuffer" , js_name = mapWriteAsync ) ]
    #[doc = "The `mapWriteAsync()` method."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/GPUBuffer/mapWriteAsync)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `GpuBuffer`*"]
    #[doc = ""]
    #[doc = "*This API is unstable and requires `--cfg=web_sys_unstable_apis` to be activated, as"]
    #[doc = "[described in the `wasm-bindgen` guide](https://rustwasm.github.io/docs/wasm-bindgen/web-sys/unstable-apis.html)*"]
    pub fn map_write_async(this: &GpuBuffer) -> ::js_sys::Promise;
    #[cfg(web_sys_unstable_apis)]
    # [ wasm_bindgen ( method , final , js_class = "GPUBuffer" , js_name = unmap ) ]
    #[doc = "The `unmap()` method."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/GPUBuffer/unmap)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `GpuBuffer`*"]
    #[doc = ""]
    #[doc = "*This API is unstable and requires `--cfg=web_sys_unstable_apis` to be activated, as"]
    #[doc = "[described in the `wasm-bindgen` guide](https://rustwasm.github.io/docs/wasm-bindgen/web-sys/unstable-apis.html)*"]
    pub fn unmap(this: &GpuBuffer);
}
