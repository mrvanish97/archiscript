import ArchiScriptExamples.UserRegistration

open ArchiScriptExamples.UserRegistration

def allUsers : UserStore := fun _ => True

def wrongSelection : ExistingSelection existingUserBranchWitness allUsers allUsers where
  source_is_existing := rfl
  input := .existingUser 7
  input_in_branch := rfl
  output := .selected 42
  output_in_branch := rfl
  selectedId := 42
  input_is_selected_id := rfl
  selected_was_present := trivial
  output_is_selected := rfl
  store_preserved := rfl
