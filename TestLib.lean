def tally (tests : List (String × Bool)) : IO (Nat × Nat) :=
  match tests with
  | [] => return (0, 0) 
  | (name, result) :: tests' =>  do
    let (pass_count, fail_count) <- tally tests' 
    if result then
      IO.println (s!"{name} PASSED")
      return (pass_count + 1, fail_count)
    else
      IO.println (s!"{name} FAILED")
      return (pass_count, fail_count + 1)

def test (tests : List (String × Bool)) : IO Unit := do
  let (pass_count, fail_count) <- tally (tests.reverse)
  let total <- (return pass_count + fail_count)
  IO.println s!"pass_count: {pass_count}/{total}"
  IO.println s!"fail_count: {fail_count}/{total}"
  return ()

