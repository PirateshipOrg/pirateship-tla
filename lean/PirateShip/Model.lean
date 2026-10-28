module

public import CCF.TransitionSystem
public import PirateShip.Model.Step

@[expose] public section

namespace PirateShip.Model

/-- Executable safety abstraction, with neither fairness nor an attack budget. -/
abbrev transitionSystem (c : Config) : CCF.TransitionSystem where
  State := State
  Action := Action
  init s := c.Valid /\ s = initialState c
  step := step c

end PirateShip.Model
