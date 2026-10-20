theorem ex_1_14 (p q r : Prop) (h1 : p → (q → r)) : p ∧ q → r := by
  intro h2                  -- assume p ∧ q
  have h3 : p := h2.left    -- ∧e1
  have h4 : q := h2.right   -- ∧e2
  have h5 : q → r := h1 h3  -- →e 1,3
  have h6 : r := h5 h4      -- →e 5,4
  exact h6
