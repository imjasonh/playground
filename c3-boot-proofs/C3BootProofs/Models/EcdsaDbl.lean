import C3BootProofs.Models.EcdsaRcb
import C3BootProofs.Ring.Tactic

namespace C3.Models

theorem rcbDblPoly : RcbDblPoly := by
  intro b X Y Z
  dsimp only [rcbDblI, rcbAddI, rcbDbl, rcbAdd]
  refine ⟨?_, ?_, ?_⟩ <;> ring_eq

end C3.Models
