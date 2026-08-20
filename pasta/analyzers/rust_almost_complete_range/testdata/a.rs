fn chars() {
    let _az = 'a'..'z'; // want "almost a complete range"
    let _az_inc = 'a'..='z';
    let _partial = 'a'..'y';
    let _AZ = 'A'..'Z'; // want "almost a complete range"
    let _digits = '0'..'9'; // want "almost a complete range"
    let _digits_inc = '0'..='9';
}
