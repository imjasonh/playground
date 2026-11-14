# wehadababyitsaboy: a dead simple, dead cheap usage tracking nanoframework

### First, some background

In the waning days of the late 1900s, it used to cost money to make a phone call to someone far away. A "phone call" was when someone talked into a wire and at their voice would come out the other end of the wire, at a friend's house. A "friend" was -- ... nevermind this is going to get old fast. You get the idea.

Anyway, back in those days, calling someone nearby was easy, but the further away the recipient was, the more tired the gremlins that powered the phone call got, and they demanded more money for their effort. This was called a "long distance call".

If you still wanted to communicate auditory information to someone far away and did not want to pay for that privilege, you could perform a "collect call". This meant that the _receiver_ paid the bill, not the _caller_. You'd call a number like [1-800-COLLECT](https://en.wikipedia.org/wiki/1-800-COLLECT) -- who advertised mercilessly on every television station! -- and record a brief message saying who was calling, and if the recipient liked you, they would accept the call and agree to pay for the long distance call. Sure, fine. This must have been wildly profitable for the phone company, because, again, they advertised it constantly.

Eventually the long distance phone call gremlins must have got stronger, or negotiated poorly, because long distance calls are no longer A Thing. Phone companies are still wildly profitable and still advertise incessantly, don't worry.

But before the practice of collect calls was crumpled up and tossed into the ash heap of history, they were responsible for one last pop culture grenade, in the form of a car insurance commercial:

https://youtu.be/j0ULftC7ndM?si=gXcg9Q5dUq8_blCk&t=1530

_(skip to 25:30 if that doesn't work)_

The joke is that if you're super cheap, and can convey all the important information in that short recording to convince the recipient to accept the call, and the recipient doesn't even need to accept the call or pay anything. You can finally get one over on those rapacious telecommunications vendors!

You can learn more here: https://geicocarinsurance.fandom.com/wiki/Bob_Wehadababyitsaboy -- did you know that the GEICO insurance company has a fandom.com site? And presumably, by extension, a fandom?

### Anyway!

I had an idea last night to cheaply report and collect basic user tracking data by ~abusing~ relying on a not-well-known fact about GCS buckets (and, S3 buckets, if that's your thing).

Did you know that if you configure your bucket just so, requests for missing objects can get recorded in usage logs? This is presumably useful for something like tracking 404 requests on your website or something, but in this case, it also means you can send any request you want to a bucket, anonymously, serve no data, incur almost no cost, and record that data? Now you do!

I made a little demo in this repo, and it's called `wehadababyitsaboy`. Get it?

For web clients, you can embed [`whbiab.js`](https://raw.githubusercontent.com/imjasonh/playground/refs/heads/main/wehadababyitsaboy/web/whbiab.js) (pronounced WEE-bee-ab) and it'll collect whatever it can about the page and send a 404 request to the tracking bucket. Google will then record that 404 in CSV logs. It's embedded in all the browser apps in this repo, including this blog.

For Go clients, there's a [`cobra`](https://github.com/spf13/cobra)-compatible [helper library](https://github.com/imjasonh/playground/tree/main/wehadababyitsaboy/go) to do the same. For Rust, there's a [`clap`](https://github.com/clap-rs/clap)-compatible [helper module](https://github.com/imjasonh/playground/tree/main/wehadababyitsaboy/rust) to do the same. They're used by most of the CLIs in this repo.

It costs about $.05 per million recorded requests, or _1/80th_ of what a _single minute_ of long distance collect calling used to cost. Crazy.

If you want to set this up for yourself, you're free to. Everything's [defined in Terraform](https://github.com/imjasonh/playground/tree/main/wehadababyitsaboy/terraform), all you need is a GCP project and a dream.

I haven't set up any kind of thing to actually sift through the request logs yet, but maybe I'll get around to it once I have some collected. It'd be cool to see who else is here.

Is tracking kinda sketchy and dubiously useful, and somewhat trivially circumvented? Yeah, sure is. If you don't want it, you can set `DO_NOT_TRACK=1` or [in your browser settings](https://support.google.com/chrome/answer/2790761?ai1hc=1). That's fine by me.

Still, I think it's useful for CLI authors and web toy makers to see whether anybody else is actually using these things, and if so how. I trust my little GCS toy more than I trust some third party, and it was fun to make. A little nostalgia and whimsy is good for the soul.

### Epilogue

That YouTube link up there (if it's still up) is just a recording of what TV was like in the early 2000s. The commercial before that GEICO one was for lightbulbs. Different time!
