class Base {}

class NeedsSuper extends Base { constructor() { this.x = 1 } } // want "subclass constructor must call super()"
