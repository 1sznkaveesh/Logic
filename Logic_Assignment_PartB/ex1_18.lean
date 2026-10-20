theorem ex_1_18 (p q r : Prop) (h1 : p ∧ (q ∨ r)) : (p ∧ q) ∨ (p ∧ r) := by
  have h2 : p := h1.left
  have h3 : q ∨ r := h1.right
  cases h3 with
  | inl h4 =>                              -- assume q
    have h5 : p ∧ q := And.intro h2 h4
    exact Or.inl h5
  | inr h7 =>                              -- assume r
    have h8 : p ∧ r := And.intro h2 h7
    exact Or.inr h8
