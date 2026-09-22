# Laya / Jev autopilot bridge.
# The Node client writes /laya/cmd/*. This addon copies those onto the
# real control properties while the stamp is fresh.

var LOG = LOG_INFO;

var main = func(addon) {
    logprint(LOG, "fg-laya addon from ", addon.basePath);

    props.globals.initNode("/laya/enabled", 1, "BOOL");
    props.globals.initNode("/laya/backend", "waiting", "STRING");
    props.globals.initNode("/laya/last-choice", "", "STRING");
    props.globals.initNode("/laya/cmd/aileron", 0, "DOUBLE");
    props.globals.initNode("/laya/cmd/elevator", 0, "DOUBLE");
    props.globals.initNode("/laya/cmd/rudder", 0, "DOUBLE");
    props.globals.initNode("/laya/cmd/throttle", 0.7, "DOUBLE");
    props.globals.initNode("/laya/cmd/stamp", 0, "INT");

    var apply = func {
        if (!getprop("/laya/enabled")) {
            return;
        }
        var stamp = getprop("/laya/cmd/stamp") or 0;
        if (stamp <= 0) {
            return;
        }
        var now = systime();
        if (now - stamp > 3) {
            return;
        }
        setprop("/controls/flight/aileron", getprop("/laya/cmd/aileron"));
        setprop("/controls/flight/elevator", getprop("/laya/cmd/elevator"));
        setprop("/controls/flight/rudder", getprop("/laya/cmd/rudder"));
        setprop("/controls/engines/engine/throttle", getprop("/laya/cmd/throttle"));
        setprop("/controls/gear/gear-down", 0);
        setprop("/autopilot/locks/heading", "");
        setprop("/autopilot/locks/altitude", "");
        setprop("/autopilot/locks/speed", "");
    };

    var timer = maketimer(0.05, apply);
    timer.simulatedTime = 1;
    timer.start();

    setlistener("/sim/signals/fdm-initialized", func {
        logprint(LOG, "fg-laya waiting for /laya/cmd/stamp from the Node client");
    }, 1, 0);
};
