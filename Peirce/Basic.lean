/-- 排中律 -/
def ExcludedMiddle : Prop := ∀ P : Prop, P ∨ ¬P

/-- 二重否定除去則 -/
def DoubleNegElim : Prop := ∀ P : Prop, ¬¬P → P

/-- パースの法則 -/
def PeirceLaw : Prop := ∀ P Q : Prop, ((P → Q) → P) → P

/-- 排中律から二重否定除去則が導ける -/
theorem excluded_middle_implies_double_neg_elim : ExcludedMiddle → DoubleNegElim := by
  -- 排中律を仮定する
  intro excluded_middle

  -- 命題 P が任意に与えられたとする
  intro P

  -- 仮定より排中律 P ∨ ¬ P が成り立つ
  have h : P ∨ ¬ P := excluded_middle P

  -- ¬¬ P を仮定する
  intro h2np

  -- 排中律の場合分け
  cases h with
  | inl pos =>
    exact pos
  | inr neg =>
    exfalso
    exact h2np neg

/-- 二重否定除去則からパースの法則が導ける -/
theorem double_neg_elim_implies_peirce_law : DoubleNegElim → PeirceLaw := by
  -- 二重否定除去則を仮定する
  intro double_neg_elim

  -- 命題 P, Q が任意に与えられたとする
  intro P Q

  -- (P → Q) → P を仮定する
  intro hpqp

  -- 二重否定除去則より ¬¬ P → P
  have h : ¬¬ P → P := double_neg_elim P

  -- ¬¬ P を示す
  apply h

  -- ¬ P を仮定する
  intro hnp

  -- ¬ P から P → Q を示す
  have hpq : P → Q := by
    intro hp
    exfalso 
    contradiction

  -- (P → Q) → P と P → Q から P を得る
  have hp : P := by exact hpqp hpq

  contradiction

/-- パースの法則から排中律が導ける -/
theorem peirce_law_implies_excluded_middle : PeirceLaw → ExcludedMiddle := by
  -- パースの法則を仮定する
  -- ((P → Q) → P) → P
  intro peirce_law

  -- 命題 P が任意に与えられたとする
  intro P

  -- goal を T と置く
  let T := P ∨ ¬ P

  -- パースの法則 ((X → Y) → X) → Y において
  -- X = P ∨ ¬ P (= T), Y = ¬ P としたものを仮定に置く
  have h : ((T → ¬ P) → T) → T := peirce_law T ¬ P
  
  -- 仮定 ((T → ¬ P) → T) → T からゴール T を導けば良いので
  -- (T → ¬ P) → T を示せば十分  
  suffices (T → ¬ P) → T by exact h this

  -- T → ¬ P を仮定する
  intro htnp
  
  -- ¬ P を示す
  right

  -- P を仮定する
  intro hp

  -- (P ∨ ¬ P) → ¬ P に P を適用することで ¬ P を得る 
  have hnp : ¬ P := by
    -- T を示す
    apply htnp

    -- P を示す
    left

    -- P は仮定にすでにある
    exact hp

  -- 仮定に P と ¬ P が両立したので矛盾 
  contradiction
