const sok = { set sy(v) { this.y = v } }
class C { set sy(v) { this.y = v } }
const notSetter = {
  listenerCount(type) {
    const set = type
    return set ? 1 : 0
  },
}
function setup() { return 1 }
