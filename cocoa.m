# cocoa ui in mac os x

main _ =
  dlopen = Dl 'dlopen'
  Fun.call1 dlopen '/System/Library/Frameworks/Cocoa.framework/Versions/A/Cocoa' # must load before CoreFoundation or AppKit
  msg = Dl 'objc_msgSend'
  class = Dl 'objc_getClass'
  sel = Dl 'sel_getUid'
  app = Fun.call2 msg (Fun.call1 class 'NSApplication') (Fun.call1 sel 'sharedApplication')
  Fun.call3 msg app (Fun.call1 sel 'setActivationPolicy:') 1
  win = Fun.call2 msg (Fun.call1 class 'NSWindow') (Fun.call1 sel 'alloc')
  Fun.call5x 04069_0000_0000_0000 msg.Cast.any win (Fun.call1 sel 'initWithContentRect:styleMask:backing:defer:') 1 2 0 # GRect
  title = Fun.call3 msg (Fun.call1 class 'NSString') (Fun.call1 sel 'stringWithUTF8String:') 'hello'.S.mem
  Fun.call3 msg win (Fun.call1 sel 'setTitle:') title
  Fun.call3 msg win (Fun.call1 sel 'makeKeyAndOrderFront:') 0
  Fun.call3 msg app (Fun.call1 sel 'activateIgnoringOtherApps:') 1
  Fun.call2 msg app (Fun.call1 sel 'run')                                               # failed if [Dl 'NSApp'], not [app]
  # killall -9 min
