theorem ex_1_17 (p q r : Prop) (h1 : (p ∨ q) ∨ r) : p ∨ (q ∨ r) := by
  cases h1 with
  | inl h2 =>                          -- assume p ∨ q
    cases h2 with
    | inl h3 =>                        -- assume p
      exact Or.inl h3                  -- ∨i1: p ∨ (q ∨ r)
    | inr h5 =>                        -- assume q
      have h6 : q ∨ r := Or.inl h5     -- ∨i1: q ∨ r
      exact Or.inr h6                  -- ∨i2: p ∨ (q ∨ r)
  | inr h9 =>                          -- assume r
    have h10 : q ∨ r := Or.inr h9      -- ∨i2: q ∨ r
    exact Or.inr h10                   -- ∨i2: p ∨ (q ∨ r)
