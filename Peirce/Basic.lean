def LEM : Prop := ∀ P : Prop, P ∨ ¬P

def DN : Prop := ∀ P : Prop, ¬¬P → P

def Peirce : Prop := ∀ P Q : Prop, ((P → Q) → P) → P

theorem lem_implies_dn : LEM → DN := by sorry

theorem dn_implies_peirce : DN → Peirce := by sorry  

theorem peirce_implies_lem : Peirce → LEM := by sorry
