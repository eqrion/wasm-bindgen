#![allow(unused_imports)]
use super::*;
use wasm_bindgen::prelude::*;
#[wasm_bindgen]
extern "C" {
    # [ wasm_bindgen ( extends = EventTarget , extends = :: js_sys :: Object , js_name = Animation , typescript_type = "Animation" ) ]
    #[derive(Debug, Clone, PartialEq, Eq)]
    #[doc = "The `Animation` class."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub type Animation;
    # [ wasm_bindgen ( final , method , getter , js_class = "Animation" , js_name = id ) ]
    #[doc = "Getter for the `id` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/id)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn id(this: &Animation) -> String;
    # [ wasm_bindgen ( final , method , setter , js_class = "Animation" , js_name = id ) ]
    #[doc = "Setter for the `id` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/id)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn set_id(this: &Animation, value: &str);
    #[cfg(feature = "AnimationEffect")]
    # [ wasm_bindgen ( final , method , getter , js_class = "Animation" , js_name = effect ) ]
    #[doc = "Getter for the `effect` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/effect)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`, `AnimationEffect`*"]
    pub fn effect(this: &Animation) -> Option<AnimationEffect>;
    #[cfg(feature = "AnimationEffect")]
    # [ wasm_bindgen ( final , method , setter , js_class = "Animation" , js_name = effect ) ]
    #[doc = "Setter for the `effect` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/effect)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`, `AnimationEffect`*"]
    pub fn set_effect(this: &Animation, value: Option<&AnimationEffect>);
    #[cfg(feature = "AnimationTimeline")]
    # [ wasm_bindgen ( final , method , getter , js_class = "Animation" , js_name = timeline ) ]
    #[doc = "Getter for the `timeline` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/timeline)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`, `AnimationTimeline`*"]
    pub fn timeline(this: &Animation) -> Option<AnimationTimeline>;
    #[cfg(feature = "AnimationTimeline")]
    # [ wasm_bindgen ( final , method , setter , js_class = "Animation" , js_name = timeline ) ]
    #[doc = "Setter for the `timeline` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/timeline)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`, `AnimationTimeline`*"]
    pub fn set_timeline(this: &Animation, value: Option<&AnimationTimeline>);
    # [ wasm_bindgen ( final , method , getter , js_class = "Animation" , js_name = startTime ) ]
    #[doc = "Getter for the `startTime` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/startTime)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn start_time(this: &Animation) -> Option<f64>;
    # [ wasm_bindgen ( final , method , setter , js_class = "Animation" , js_name = startTime ) ]
    #[doc = "Setter for the `startTime` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/startTime)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn set_start_time(this: &Animation, value: Option<f64>);
    # [ wasm_bindgen ( final , method , getter , js_class = "Animation" , js_name = currentTime ) ]
    #[doc = "Getter for the `currentTime` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/currentTime)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn current_time(this: &Animation) -> Option<f64>;
    # [ wasm_bindgen ( final , method , setter , js_class = "Animation" , js_name = currentTime ) ]
    #[doc = "Setter for the `currentTime` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/currentTime)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn set_current_time(this: &Animation, value: Option<f64>);
    # [ wasm_bindgen ( final , method , getter , js_class = "Animation" , js_name = playbackRate ) ]
    #[doc = "Getter for the `playbackRate` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/playbackRate)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn playback_rate(this: &Animation) -> f64;
    # [ wasm_bindgen ( final , method , setter , js_class = "Animation" , js_name = playbackRate ) ]
    #[doc = "Setter for the `playbackRate` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/playbackRate)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn set_playback_rate(this: &Animation, value: f64);
    #[cfg(feature = "AnimationPlayState")]
    # [ wasm_bindgen ( final , method , getter , js_class = "Animation" , js_name = playState ) ]
    #[doc = "Getter for the `playState` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/playState)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`, `AnimationPlayState`*"]
    pub fn play_state(this: &Animation) -> AnimationPlayState;
    # [ wasm_bindgen ( final , method , getter , js_class = "Animation" , js_name = pending ) ]
    #[doc = "Getter for the `pending` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/pending)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn pending(this: &Animation) -> bool;
    # [ wasm_bindgen ( final , catch , method , getter , js_class = "Animation" , js_name = ready ) ]
    #[doc = "Getter for the `ready` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/ready)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn ready(this: &Animation) -> Result<::js_sys::Promise, JsValue>;
    # [ wasm_bindgen ( final , catch , method , getter , js_class = "Animation" , js_name = finished ) ]
    #[doc = "Getter for the `finished` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/finished)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn finished(this: &Animation) -> Result<::js_sys::Promise, JsValue>;
    # [ wasm_bindgen ( final , method , getter , js_class = "Animation" , js_name = onfinish ) ]
    #[doc = "Getter for the `onfinish` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/onfinish)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn onfinish(this: &Animation) -> Option<::js_sys::Function>;
    # [ wasm_bindgen ( final , method , setter , js_class = "Animation" , js_name = onfinish ) ]
    #[doc = "Setter for the `onfinish` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/onfinish)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn set_onfinish(this: &Animation, value: Option<&::js_sys::Function>);
    # [ wasm_bindgen ( final , method , getter , js_class = "Animation" , js_name = oncancel ) ]
    #[doc = "Getter for the `oncancel` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/oncancel)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn oncancel(this: &Animation) -> Option<::js_sys::Function>;
    # [ wasm_bindgen ( final , method , setter , js_class = "Animation" , js_name = oncancel ) ]
    #[doc = "Setter for the `oncancel` field of this object."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/oncancel)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn set_oncancel(this: &Animation, value: Option<&::js_sys::Function>);
    #[wasm_bindgen(catch, constructor, js_class = "Animation")]
    #[doc = "The `new Animation(..)` constructor, creating a new instance of `Animation`."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/Animation)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn new() -> Result<Animation, JsValue>;
    #[cfg(feature = "AnimationEffect")]
    #[wasm_bindgen(catch, constructor, js_class = "Animation")]
    #[doc = "The `new Animation(..)` constructor, creating a new instance of `Animation`."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/Animation)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`, `AnimationEffect`*"]
    pub fn new_with_effect(effect: Option<&AnimationEffect>) -> Result<Animation, JsValue>;
    #[cfg(all(feature = "AnimationEffect", feature = "AnimationTimeline",))]
    #[wasm_bindgen(catch, constructor, js_class = "Animation")]
    #[doc = "The `new Animation(..)` constructor, creating a new instance of `Animation`."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/Animation)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`, `AnimationEffect`, `AnimationTimeline`*"]
    pub fn new_with_effect_and_timeline(
        effect: Option<&AnimationEffect>,
        timeline: Option<&AnimationTimeline>,
    ) -> Result<Animation, JsValue>;
    # [ wasm_bindgen ( method , final , js_class = "Animation" , js_name = cancel ) ]
    #[doc = "The `cancel()` method."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/cancel)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn cancel(this: &Animation);
    # [ wasm_bindgen ( catch , method , final , js_class = "Animation" , js_name = finish ) ]
    #[doc = "The `finish()` method."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/finish)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn finish(this: &Animation) -> Result<(), JsValue>;
    # [ wasm_bindgen ( catch , method , final , js_class = "Animation" , js_name = pause ) ]
    #[doc = "The `pause()` method."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/pause)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn pause(this: &Animation) -> Result<(), JsValue>;
    # [ wasm_bindgen ( catch , method , final , js_class = "Animation" , js_name = play ) ]
    #[doc = "The `play()` method."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/play)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn play(this: &Animation) -> Result<(), JsValue>;
    # [ wasm_bindgen ( catch , method , final , js_class = "Animation" , js_name = reverse ) ]
    #[doc = "The `reverse()` method."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/reverse)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn reverse(this: &Animation) -> Result<(), JsValue>;
    # [ wasm_bindgen ( method , final , js_class = "Animation" , js_name = updatePlaybackRate ) ]
    #[doc = "The `updatePlaybackRate()` method."]
    #[doc = ""]
    #[doc = "[MDN Documentation](https://developer.mozilla.org/en-US/docs/Web/API/Animation/updatePlaybackRate)"]
    #[doc = ""]
    #[doc = "*This API requires the following crate features to be activated: `Animation`*"]
    pub fn update_playback_rate(this: &Animation, playback_rate: f64);
}
