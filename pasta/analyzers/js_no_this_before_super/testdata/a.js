class Base {}

class SubBad extends Base { constructor() { this.x = 1; super() } } // want "this or super property before super() in a subclass constructor"
