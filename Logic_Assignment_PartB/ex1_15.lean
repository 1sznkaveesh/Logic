theorem ex_1_15 (p q r : Prop) (h1 : p → q) : p ∧ r → q ∧ r := by
  intro h2                 --assume p ∧ r
  have h3 : p := h2.left   -- ∧e1
  have h4 : r := h2.right  -- ∧e2
  have h5 : q := h1 h3     -- →e 1,3
  exact And.intro h5 h4    -- ∧i 5,4
