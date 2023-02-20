def tally (tests : List (String × Bool)) : IO (Nat × Nat) :=
  match tests with
  | [] => return (0, 0) 
  | (name, result) :: tests' =>  do
    let (pass_count, fail_count) <- tally tests' 
    if result then
      IO.println (s!"✓ {name}")
      return (pass_count + 1, fail_count)
    else
      IO.println (s!"× {name}")
      return (pass_count, fail_count + 1)

def test (name : String) (tests : List (String × Bool)) : IO Unit := do

  IO.println "----------------------------------------------" 
  IO.println s!"{name}:"
  let (pass_count, fail_count) <- tally (tests.reverse)
  let total := pass_count + fail_count
  IO.println s!"pass count: {pass_count}/{total}"
  IO.println s!"fail count: {fail_count}/{total}"
  let summary := (
    if fail_count > 0 then
      "FAIL"
    else
      "ok"
  )

  IO.println s!"summary: {summary}"
  IO.println "----------------------------------------------" 
  return ()

