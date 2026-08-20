function use(value) { return value }

function case_js_for_direction_1() {
    for (let i = 0; i < 10; i--) { use(i) } // want "for-loop update moves the counter the wrong way"
}
function case_js_for_direction_up_2() {
    for (let k = 10; k > 0; k++) { use(k) } // want "for-loop ++ with a > test moves the wrong way"
}
