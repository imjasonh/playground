<?php
function show($user) {
    var_dump($user); // want "debug output should not be committed"
    print_r($user);  // want "debug output should not be committed"
    echo $user->name;
}
