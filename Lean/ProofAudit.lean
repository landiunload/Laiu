import Laiu
import Lean

open Lean Elab Command

run_cmd
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let declarations := env.constants.toList.filter fun (name, _) =>
    `Laiu |>.isPrefixOf (privateToUserName name)
  if declarations.isEmpty then
    throwError "No Laiu declarations found"
  for (name, _) in declarations do
    let additional := (← collectAxioms name).filter (!allowed.contains ·)
    unless additional.isEmpty do
      throwError "{name} relies on nonstandard axioms: {additional}"
  logInfo m!"Axioms checked for {declarations.length} Laiu declarations"
