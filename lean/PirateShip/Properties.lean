module

public import PirateShip.Properties.Defs
public import PirateShip.Proofs.Foundations

@[expose] public section

namespace PirateShip.Properties

open Model

/-- Valid executions cannot rewrite already published block records. -/
theorem published_blocks_persist (c : Config) (before after : State) (a : Action)
    (transition : (transitionSystem c).step before a = some after) :
    before.blocks.IsPrefix after.blocks := by
  exact Proofs.step_blocks_prefix c before after a transition

/-- Valid executions cannot erase previously issued authentication evidence. -/
theorem signatures_persist (c : Config) (before after : State) (a : Action)
    (transition : (transitionSystem c).step before a = some after) :
    before.signatures.IsPrefix after.signatures := by
  exact Proofs.step_signatures_prefix c before after a transition

end PirateShip.Properties
