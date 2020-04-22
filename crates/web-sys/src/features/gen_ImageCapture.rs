#![allow(unused_imports)]
use super::*;
use wasm_bindgen::prelude::*;
#[wasm_bindgen]
extern "C" {
    # [ wasm_bindgen ( extends = EventTarget , extends = :: js_sys :: Object , js_name = ImageCapture , typescript_type = "ImageCapture" ) ]
    #[derive(Debug, Clone, PartialEq, Eq)]
    #[doc = "The `ImageCapture` class."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/ImageCapture)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `ImageCapture`*"]
    pub type ImageCapture;
    #[cfg(feature = "VideoStreamTrack")]
    # [ wasm_bindgen ( final , method , getter , js_class = "ImageCapture" , js_name = videoStreamTrack ) ]
    #[doc = "Getter for the `videoStreamTrack` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/ImageCapture/videoStreamTrack)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `ImageCapture`, `VideoStreamTrack`*"]
    pub fn video_stream_track(this: &ImageCapture) -> VideoStreamTrack;
    # [ wasm_bindgen ( final , method , getter , js_class = "ImageCapture" , js_name = onphoto ) ]
    #[doc = "Getter for the `onphoto` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/ImageCapture/onphoto)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `ImageCapture`*"]
    pub fn onphoto(this: &ImageCapture) -> Option<::js_sys::Function>;
    # [ wasm_bindgen ( final , method , setter , js_class = "ImageCapture" , js_name = onphoto ) ]
    #[doc = "Setter for the `onphoto` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/ImageCapture/onphoto)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `ImageCapture`*"]
    pub fn set_onphoto(this: &ImageCapture, value: Option<&::js_sys::Function>);
    # [ wasm_bindgen ( final , method , getter , js_class = "ImageCapture" , js_name = onerror ) ]
    #[doc = "Getter for the `onerror` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/ImageCapture/onerror)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `ImageCapture`*"]
    pub fn onerror(this: &ImageCapture) -> Option<::js_sys::Function>;
    # [ wasm_bindgen ( final , method , setter , js_class = "ImageCapture" , js_name = onerror ) ]
    #[doc = "Setter for the `onerror` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/ImageCapture/onerror)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `ImageCapture`*"]
    pub fn set_onerror(this: &ImageCapture, value: Option<&::js_sys::Function>);
    #[cfg(feature = "VideoStreamTrack")]
    #[wasm_bindgen(catch, constructor, js_class = "ImageCapture")]
    #[doc = "The `new ImageCapture(..)` constructor, creating a new instance of `ImageCapture`."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/ImageCapture/ImageCapture)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `ImageCapture`, `VideoStreamTrack`*"]
    pub fn new(track: &VideoStreamTrack) -> Result<ImageCapture, JsValue>;
    # [ wasm_bindgen ( catch , method , final , js_class = "ImageCapture" , js_name = takePhoto ) ]
    #[doc = "The `takePhoto()` method."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/ImageCapture/takePhoto)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `ImageCapture`*"]
    pub fn take_photo(this: &ImageCapture) -> Result<(), JsValue>;
}