# Introducing Inkbot

Everyone seems to be hopping on the ESP32 bandwagon these days. They've been cool for a while now, due to them being relatively cheap, relatively powerful, and widely available. But I think the real gasoline on the bonfire has been the introduction of coding agents capable of translating ideas into embedded code in a matter of minutes. Coding agents are almost literally born and bred to be able to understand and write code for these little devices! Unfortunately I was only born and bred to write backend code that moves bits from one place to another place in a slightly different shape, ideally correctly, securely and quickly. Sometimes I get to make a little red X turn into a green checkmark. If I'm lucky!

Anyway, I'm not immune to this ESP32 hype. While I was between jobs I toyed with [signed over-the-air (OTA) updates automated with GitHub Actions](http://github.com/imjasonh/esp32), but at the end all it did was blink and log that it was working. It was fun, and I learned a lot from the experience, but in the end it was ...uninspiring. 

A few weeks ago, [a guy on Twitter started doing more cool shit with ESP32s, and most importantly, posting about it and getting other folks jazzed about doing cool shit with ESP32s](https://x.com/steveruizok/status/2085480605278515656). It was then that I knew The Fever had returned.

I was a little less interested in building LCD fluid simulations and tiny Flappy Birds or custom Tamagotchis (though those are cool, admittedly). Instead I got interested in e-ink displays. And I wanted something cool for my desk at work. So that's what I built!

