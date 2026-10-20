theorem ex_1_13 (p q r : Prop) (h1 : p ∧ q → r) : p → (q → r) := by
  intro hp                           -- assumption p
  intro hq                           -- assumption q
  have h4 : p ∧ q := And.intro hp hq -- ∧i 2,3
  have h5 : r := h1 h4               --→ e 1,4
  exact h5
