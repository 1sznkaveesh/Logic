theorem ex_1_16 (p q r : Prop) (h1 : q → r) : p ∨ q → p ∨ r := by
  intro h2
  cases h2 with
  | inl h3 =>                        -- box 1: assume p
    have h4 : p ∨ r := Or.inl h3     -- ∨i1
    exact h4
  | inr h5 =>                        -- box 2: assume q
    have h6 : r := h1 h5             -- →e 1,5
    have h7 : p ∨ r := Or.inr h6     -- ∨i2
    exact h7
