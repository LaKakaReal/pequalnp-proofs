import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1610

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

private def val {n : ℕ} (gates : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  Circuit.eval ⟨gates, w⟩ (List.ofFn x)

private lemma input_val {n : ℕ} (gates : List Gate) (p : Fin n) (x : Fin n → Bool) :
    val gates p x = x p := by
  change (run gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma missing_val {n : ℕ} (gates : List Gate) (w : ℕ) (x : Fin n → Bool)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  change (run gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length] using hw)

private lemma gate_val {n : ℕ} (gates : List Gate) (w : ℕ) (x : Fin n → Bool)
    (hn : n ≤ w) (hw : w < n + gates.length) :
    let g := gates[w - n]'(by omega)
    val gates w x = g.op.eval (g.inputs.map fun r => if r < w then val gates r x else false) := by
  let j := w - n
  have hj : j < gates.length := by omega
  let g := gates[j]
  let earlier := run (gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run gates (List.ofFn x) = run (g :: gates.drop (j + 1)) earlier := by
    rw [run_split gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then val gates r x else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then val gates r x else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

private lemma val_mono {n : ℕ} (gates : List Gate)
    (hvalid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true) :
    ∀ w : ℕ, val gates w x = true → val gates w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx
    by_cases hlt : w < n
    · have hx' : val gates (⟨w, hlt⟩ : Fin n) x = true := hx
      rw [input_val] at hx'
      have hy' : val gates (⟨w, hlt⟩ : Fin n) y = true := by
        rw [input_val]; exact hxy ⟨w, hlt⟩ hx'
      exact hy'
    · by_cases hlt2 : w < n + gates.length
      · have hn : n ≤ w := by omega
        have hj : w - n < gates.length := by omega
        have hop := (hvalid (gates[w - n]'hj) (List.getElem_mem hj)).1
        rw [gate_val gates w x hn hlt2] at hx
        rw [gate_val gates w y hn hlt2]
        have hstep (r : ℕ) :
            (if r < w then val gates r x else false) = true →
            (if r < w then val gates r y else false) = true := by
          by_cases hr : r < w
          · simpa [hr] using ih r hr
          · simp [hr]
        rcases hop with hop | hop
        · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
          intro b hb
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
          exact hstep r (hx _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
        · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
          obtain ⟨b, hb, rfl⟩ := hx
          obtain ⟨r, hr, hrv⟩ := List.mem_map.mp hb
          exact ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, hstep r hrv⟩
      · rw [missing_val gates w x (by omega)] at hx
        exact Bool.noConfusion hx

private lemma or_pair_false {n : ℕ} (gates : List Gate)
    (g : Fin gates.length) (w1 w2 : ℕ)
    (hop : (gates.get g).op = GateOp.or)
    (hin : (gates.get g).inputs = [w1, w2])
    (hw1 : w1 < n + (g : ℕ)) (hw2 : w2 < n + (g : ℕ))
    (x : Fin n → Bool)
    (hfalse : val gates (n + (g : ℕ)) x = false) :
    val gates w1 x = false ∧ val gates w2 x = false := by
  have hg := gate_val gates (n + (g : ℕ)) x (by omega) (by have := g.isLt; omega)
  simp only [Nat.add_sub_cancel_left] at hg
  have hget : gates[(g : ℕ)]'(g.isLt) = gates.get g := rfl
  rw [hget, hop, hin] at hg
  simp only [List.map_cons, List.map_nil, hw1, hw2, ↓reduceIte, GateOp.eval, List.any_cons,
    List.any_nil, id_eq, Bool.or_false] at hg
  rw [hfalse] at hg
  exact Bool.or_eq_false_iff.mp hg.symm

private lemma active_mem_insert_D {n : ℕ} (L M : Finset (Fin n)) (m : Fin n)
    (t : Fin n → Fin n → Bool) (gates : List Gate)
    (hLM : L ∩ M = {m})
    (hvalid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hwM : val gates w (fun v : Fin n => decide (v ∉ M)) = false)
    (r : Fin n) (hrL : r ∈ L) (hwr : val gates w (t r) = true) :
    r ∈ insert m ((L \ M).filter (fun r => ∃ v ∈ M, t r v = true)) := by
  by_cases hrM : r ∈ M
  · have hm : r = m := by
      have h1 : r ∈ L ∩ M := Finset.mem_inter.mpr ⟨hrL, hrM⟩
      rw [hLM] at h1
      exact Finset.mem_singleton.mp h1
    exact Finset.mem_insert.mpr (Or.inl hm)
  · apply Finset.mem_insert.mpr
    apply Or.inr
    refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hrL, hrM⟩, ?_⟩
    by_contra hno
    push Not at hno
    have hle : ∀ v : Fin n, t r v = true → decide (v ∉ M) = true := by
      intro v hv
      apply decide_eq_true
      intro hvM
      exact hno v hvM hv
    have htrue := val_mono gates hvalid (t r) (fun v => decide (v ∉ M)) hle w hwr
    rw [hwM] at htrue
    exact Bool.noConfusion htrue

private def edge {n : ℕ} (L : Finset (Fin n)) (t : Fin n → Fin n → Bool)
    (gates : List Gate) (k : ℕ) (y y' : Fin n) : Prop :=
  y ∈ L ∧ y' ∈ L ∧
  ∃ i : Fin gates.length, (i : ℕ) < k ∧
    (gates.get i).op = GateOp.or ∧
    val gates (n + (i : ℕ)) (fun v : Fin n => decide (v ∉ L)) = false ∧
    ∃ a b : ℕ, (gates.get i).inputs = [a, b] ∧
      (val gates a (t y) = true ∨ val gates b (t y) = true) ∧
      (val gates a (t y') = true ∨ val gates b (t y') = true)

private def equiv {n : ℕ} (L : Finset (Fin n)) (t : Fin n → Fin n → Bool)
    (gates : List Gate) (k : ℕ) : Fin n → Fin n → Prop :=
  Relation.EqvGen (edge L t gates k)

private lemma equiv_zero_iff {n : ℕ} (L : Finset (Fin n)) (t : Fin n → Fin n → Bool)
    (gates : List Gate) (x y : Fin n) :
    equiv L t gates 0 x y ↔ x = y := by
  constructor
  · intro h
    induction h with
    | rel a b hab =>
      obtain ⟨_, _, i, hi, _⟩ := hab
      omega
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  · rintro rfl
    exact Relation.EqvGen.refl x

private lemma equiv_mono {n : ℕ} (L : Finset (Fin n)) (t : Fin n → Fin n → Bool)
    (gates : List Gate) {k1 k2 : ℕ} (hk : k1 ≤ k2) {x y : Fin n}
    (h : equiv L t gates k1 x y) : equiv L t gates k2 x y := by
  induction h with
  | rel a b hab =>
    obtain ⟨ha, hb, i, hi, hop, hz, c, d, hin, h1, h2⟩ := hab
    exact Relation.EqvGen.rel a b ⟨ha, hb, i, lt_of_lt_of_le hi hk, hop, hz, c, d, hin, h1, h2⟩
  | refl a => exact Relation.EqvGen.refl a
  | symm a b _ ih => exact Relation.EqvGen.symm a b ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans a b c ih1 ih2

private lemma equiv_preserves {n : ℕ} (L : Finset (Fin n)) (t : Fin n → Fin n → Bool)
    (gates : List Gate) (k : ℕ) (X : Finset (Fin n))
    (hX : ∀ y y', edge L t gates k y y' → (y ∈ X ↔ y' ∈ X))
    {a b : Fin n} (hab : equiv L t gates k a b) : a ∈ X ↔ b ∈ X := by
  induction hab with
  | rel x y hxy => exact hX x y hxy
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

private noncomputable def cls {n : ℕ} (L : Finset (Fin n)) (t : Fin n → Fin n → Bool)
    (gates : List Gate) (A : Finset (Fin n)) (k : ℕ) (x : Fin n) : Finset (Fin n) := by
  classical
  exact A.filter (fun y => equiv L t gates k x y)

private noncomputable def numClasses {n : ℕ} (L : Finset (Fin n)) (t : Fin n → Fin n → Bool)
    (gates : List Gate) (A : Finset (Fin n)) (k : ℕ) : ℕ :=
  (A.image (cls L t gates A k)).card

private lemma cls_eq_of_equiv {n : ℕ} (L : Finset (Fin n)) (t : Fin n → Fin n → Bool)
    (gates : List Gate) (A : Finset (Fin n)) (k : ℕ) {x y : Fin n}
    (h : equiv L t gates k x y) :
    cls L t gates A k x = cls L t gates A k y := by
  classical
  ext z
  simp only [cls, Finset.mem_filter]
  constructor
  · rintro ⟨hz, hxz⟩
    exact ⟨hz, Relation.EqvGen.trans y x z (Relation.EqvGen.symm x y h) hxz⟩
  · rintro ⟨hz, hyz⟩
    exact ⟨hz, Relation.EqvGen.trans x y z h hyz⟩

private lemma numClasses_zero {n : ℕ} (L : Finset (Fin n)) (t : Fin n → Fin n → Bool)
    (gates : List Gate) (A : Finset (Fin n)) :
    numClasses L t gates A 0 = A.card := by
  have hcls : ∀ x ∈ A, cls L t gates A 0 x = {x} := by
    intro x hx
    classical
    ext y
    simp only [cls, Finset.mem_filter, Finset.mem_singleton, equiv_zero_iff]
    constructor
    · rintro ⟨_, rfl⟩; rfl
    · rintro rfl; exact ⟨hx, rfl⟩
  unfold numClasses
  have himg : A.image (cls L t gates A 0) = A.image (fun x => ({x} : Finset (Fin n))) :=
    Finset.image_congr hcls
  rw [himg, Finset.card_image_of_injective _ Finset.singleton_injective]

private lemma numClasses_pos {n : ℕ} (L : Finset (Fin n)) (t : Fin n → Fin n → Bool)
    (gates : List Gate) (A : Finset (Fin n)) (hA : A.Nonempty) (k : ℕ) :
    1 ≤ numClasses L t gates A k := by
  obtain ⟨a, ha⟩ := hA
  unfold numClasses
  exact Finset.one_le_card.mpr ⟨cls L t gates A k a, Finset.mem_image_of_mem _ ha⟩

private noncomputable def stepMap {n : ℕ} (L : Finset (Fin n)) (t : Fin n → Fin n → Bool)
    (gates : List Gate) (A : Finset (Fin n)) (k : ℕ) (S : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact A.filter (fun y => ∃ x ∈ S, equiv L t gates (k + 1) x y)

private lemma stepMap_cls {n : ℕ} (L : Finset (Fin n)) (t : Fin n → Fin n → Bool)
    (gates : List Gate) (A : Finset (Fin n)) (k : ℕ) {x : Fin n} (hx : x ∈ A) :
    stepMap L t gates A k (cls L t gates A k x) = cls L t gates A (k + 1) x := by
  classical
  ext y
  simp only [stepMap, cls, Finset.mem_filter]
  constructor
  · rintro ⟨hyA, z, ⟨_, hxz⟩, hzy⟩
    exact ⟨hyA, Relation.EqvGen.trans x z y (equiv_mono L t gates (Nat.le_succ k) hxz) hzy⟩
  · rintro ⟨hyA, hxy⟩
    exact ⟨hyA, x, ⟨hx, Relation.EqvGen.refl x⟩, hxy⟩

private lemma image_step {n : ℕ} (L : Finset (Fin n)) (t : Fin n → Fin n → Bool)
    (gates : List Gate) (A : Finset (Fin n)) (k : ℕ) :
    A.image (cls L t gates A (k + 1)) =
      (A.image (cls L t gates A k)).image (stepMap L t gates A k) := by
  rw [Finset.image_image]
  apply Finset.image_congr
  intro x hx
  exact (stepMap_cls L t gates A k hx).symm

private lemma numClasses_antitone_step {n : ℕ} (L : Finset (Fin n)) (t : Fin n → Fin n → Bool)
    (gates : List Gate) (A : Finset (Fin n)) (k : ℕ) :
    numClasses L t gates A (k + 1) ≤ numClasses L t gates A k := by
  unfold numClasses
  rw [image_step L t gates A k]
  exact Finset.card_image_le

private lemma numClasses_strict_step {n : ℕ} (L : Finset (Fin n)) (t : Fin n → Fin n → Bool)
    (gates : List Gate) (A : Finset (Fin n)) (k : ℕ)
    (r r' : Fin n) (hr : r ∈ A) (hr' : r' ∈ A)
    (hneq : ¬ equiv L t gates k r r')
    (heq : equiv L t gates (k + 1) r r') :
    numClasses L t gates A (k + 1) + 1 ≤ numClasses L t gates A k := by
  let F := stepMap L t gates A k
  let Ck := A.image (cls L t gates A k)
  have hmem_r : cls L t gates A k r ∈ Ck := Finset.mem_image_of_mem _ hr
  have hmem_r' : cls L t gates A k r' ∈ Ck := Finset.mem_image_of_mem _ hr'
  have hne_cls : cls L t gates A k r ≠ cls L t gates A k r' := by
    intro h
    have hr'_in : r' ∈ cls L t gates A k r' := by
      classical
      simp only [cls, Finset.mem_filter]
      exact ⟨hr', Relation.EqvGen.refl r'⟩
    rw [← h] at hr'_in
    classical
    simp only [cls, Finset.mem_filter] at hr'_in
    exact hneq hr'_in.2
  have hF_eq : F (cls L t gates A k r) = F (cls L t gates A k r') := by
    dsimp [F]
    rw [stepMap_cls L t gates A k hr, stepMap_cls L t gates A k hr']
    exact cls_eq_of_equiv L t gates A (k + 1) heq
  have himg_eq : Ck.image F = (Ck.erase (cls L t gates A k r)).image F := by
    apply Finset.Subset.antisymm
    · intro S hS
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
      by_cases hTr : T = cls L t gates A k r
      · rw [hTr, hF_eq]
        exact Finset.mem_image.mpr
          ⟨cls L t gates A k r', Finset.mem_erase.mpr ⟨hne_cls.symm, hmem_r'⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨T, Finset.mem_erase.mpr ⟨hTr, hT⟩, rfl⟩
    · exact Finset.image_subset_image (Finset.erase_subset _ _)
  have hcard : numClasses L t gates A (k + 1) ≤ (Ck.erase (cls L t gates A k r)).card := by
    unfold numClasses
    rw [image_step L t gates A k]
    change (Ck.image F).card ≤ _
    rw [himg_eq]
    exact Finset.card_image_le
  have herase := Finset.card_erase_add_one hmem_r
  change (Ck.erase (cls L t gates A k r)).card + 1 = numClasses L t gates A k at herase
  omega

private lemma one_side {n : ℕ} (L M : Finset (Fin n)) (m : Fin n)
    (t : Fin n → Fin n → Bool) (gates : List Gate)
    (hLM : L ∩ M = {m})
    (hvalid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hearlier : ∀ i : Fin gates.length, ∀ w ∈ (gates.get i).inputs, w < n + (i : ℕ))
    (I : Finset (Fin gates.length))
    (hI : ∀ g ∈ I,
      (gates.get g).op = GateOp.or ∧
      val gates (n + (g : ℕ)) (fun v : Fin n => decide (v ∉ L)) = false ∧
      val gates (n + (g : ℕ)) (fun v : Fin n => decide (v ∉ M)) = false ∧
      ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧
        ∃ r ∈ L, ∃ r' ∈ L,
          val gates w1 (t r) = true ∧ val gates w2 (t r') = true ∧
          ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧
            ∀ i : Fin gates.length, i < g → (gates.get i).op = GateOp.or →
              val gates (n + (i : ℕ)) (fun v : Fin n => decide (v ∉ L)) = false →
              ∀ a b : ℕ, (gates.get i).inputs = [a, b] →
              ∀ y ∈ L, ∀ y' ∈ L,
                (val gates a (t y) = true ∨ val gates b (t y) = true) →
                (val gates a (t y') = true ∨ val gates b (t y') = true) →
                (y ∈ X ↔ y' ∈ X)) :
    I.card ≤ ((L \ M).filter (fun r => ∃ v ∈ M, t r v = true)).card := by
  classical
  let D := (L \ M).filter (fun r => ∃ v ∈ M, t r v = true)
  let A := insert m D
  have hm_inter : m ∈ L ∩ M := by rw [hLM]; exact Finset.mem_singleton_self m
  have hmM : m ∈ M := (Finset.mem_inter.mp hm_inter).2
  have hm_notD : m ∉ D := by
    intro h
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).2 hmM
  have hAcard : A.card = D.card + 1 := Finset.card_insert_of_notMem hm_notD
  have hAnon : A.Nonempty := ⟨m, Finset.mem_insert_self m D⟩
  have htel : ∀ N ≤ gates.length,
      (I.filter (fun g : Fin gates.length => (g : ℕ) < N)).card + numClasses L t gates A N ≤
        numClasses L t gates A 0 := by
    intro N
    induction N with
    | zero =>
      intro _
      have hempty : I.filter (fun g : Fin gates.length => (g : ℕ) < 0) = ∅ := by
        ext g; simp
      rw [hempty, Finset.card_empty, Nat.zero_add]
    | succ N ih =>
      intro hN
      have hNlt : N < gates.length := by omega
      have ih' := ih (by omega)
      let g : Fin gates.length := ⟨N, hNlt⟩
      by_cases hgI : g ∈ I
      · have hfilt : I.filter (fun x : Fin gates.length => (x : ℕ) < N + 1) =
            insert g (I.filter (fun x : Fin gates.length => (x : ℕ) < N)) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hxI, hxlt⟩
            by_cases hxe : (x : ℕ) = N
            · exact Or.inl (Fin.ext hxe)
            · exact Or.inr ⟨hxI, by omega⟩
          · rintro (rfl | ⟨hxI, hxlt⟩)
            · exact ⟨hgI, by simp [g]⟩
            · exact ⟨hxI, by omega⟩
        have hg_notin : g ∉ I.filter (fun x : Fin gates.length => (x : ℕ) < N) := by
          simp [g]
        rw [hfilt, Finset.card_insert_of_notMem hg_notin]
        obtain ⟨hop, hzL, hzM, w1, w2, hin, r, hrL, r', hr'L, hw1r, hw2r', X, hrX, hr'X, hX⟩ := hI g hgI
        have hw1lt : w1 < n + (g : ℕ) := hearlier g w1 (by rw [hin]; simp)
        have hw2lt : w2 < n + (g : ℕ) := hearlier g w2 (by rw [hin]; simp)
        obtain ⟨hw1M, hw2M⟩ := or_pair_false gates g w1 w2 hop hin hw1lt hw2lt
          (fun v => decide (v ∉ M)) hzM
        have hrA : r ∈ A := active_mem_insert_D L M m t gates hLM hvalid w1 hw1M r hrL hw1r
        have hr'A : r' ∈ A := active_mem_insert_D L M m t gates hLM hvalid w2 hw2M r' hr'L hw2r'
        have hneq : ¬ equiv L t gates N r r' := by
          intro heqv
          have hiff := equiv_preserves L t gates N X (fun y y' hedge => by
            obtain ⟨hyL, hy'L, i, hi, hiop, hizL, a, b, hiin, h1, h2⟩ := hedge
            exact hX i (Fin.lt_def.mpr hi) hiop hizL a b hiin y hyL y' hy'L h1 h2) heqv
          exact hr'X (hiff.mp hrX)
        have heq : equiv L t gates (N + 1) r r' := by
          apply Relation.EqvGen.rel
          exact ⟨hrL, hr'L, g, by simp [g], hop, hzL, w1, w2, hin, Or.inl hw1r, Or.inr hw2r'⟩
        have hdrop := numClasses_strict_step L t gates A N r r' hrA hr'A hneq heq
        omega
      · have hfilt : I.filter (fun x : Fin gates.length => (x : ℕ) < N + 1) =
            I.filter (fun x : Fin gates.length => (x : ℕ) < N) := by
          ext x
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hxI, hxlt⟩
            refine ⟨hxI, ?_⟩
            by_contra hge
            have hxe : x = g := Fin.ext (by dsimp [g]; omega)
            exact hgI (hxe ▸ hxI)
          · rintro ⟨hxI, hxlt⟩
            exact ⟨hxI, by omega⟩
        rw [hfilt]
        have hanti := numClasses_antitone_step L t gates A N
        omega
  have hfull := htel gates.length le_rfl
  have hall : I.filter (fun g : Fin gates.length => (g : ℕ) < gates.length) = I := by
    ext g
    simp
  rw [hall, numClasses_zero, hAcard] at hfull
  have hpos := numClasses_pos L t gates A hAnon gates.length
  dsimp [D] at hfull
  omega

end PEqualNP.Outside.L_meta_1610

theorem PEqualNP.Outside.L_meta_1610 : ∀ (n : ℕ) (L M : Finset (Fin n)) (m : Fin n) (t u : Fin n → Fin n → Bool)
    (gates : List PEqualNP.CircuitLowerBounds.Gate) (oL oM : ℕ),
    L ∩ M = {m} →
    (∀ r ∈ L, ∀ v ∈ L, t r v = true ↔ v = r) → (∀ r ∈ M, ∀ v ∈ M, u r v = true ↔ v = r) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < n + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, oL⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false → (∀ r ∈ L, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, oL⟩ (List.ofFn (t r)) = true) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, oM⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false → (∀ r ∈ M, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, oM⟩ (List.ofFn (u r)) = true) →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L, ∃ r' ∈ L,
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (t r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (t r')) = true ∧
          ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ ∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (i : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false → ∀ a b : ℕ, (gates.get i).inputs = [a, b] →
            ∀ y ∈ L, ∀ y' ∈ L, (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (t y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (t y)) = true) →
              (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (t y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (t y')) = true) → (y ∈ X ↔ y' ∈ X)) ∧
        ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ M, ∃ r' ∈ M,
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (u r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (u r')) = true ∧
          ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ ∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (i : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false → ∀ a b : ℕ, (gates.get i).inputs = [a, b] →
            ∀ y ∈ M, ∀ y' ∈ M, (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (u y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (u y)) = true) →
              (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (u y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (u y')) = true) → (y ∈ X ↔ y' ∈ X))) →
      I.card ≤ ((L \ M).filter (fun r => ∃ v ∈ M, t r v = true)).card ∧
      I.card ≤ ((M \ L).filter (fun r => ∃ v ∈ L, u r v = true)).card := by
  intro n L M m t u gates oL oM hLM _ht _hu hvalid hearlier _hoL0 _hoL1 _hoM0 _hoM1 I hI
  constructor
  · exact PEqualNP.Outside.L_meta_1610.one_side L M m t gates hLM hvalid hearlier I (fun g hg => by
      obtain ⟨⟨hop, hzL, hrest⟩, ⟨_, hzM, _⟩⟩ := hI g hg
      exact ⟨hop, hzL, hzM, hrest⟩)
  · exact PEqualNP.Outside.L_meta_1610.one_side M L m u gates (by rw [Finset.inter_comm]; exact hLM)
      hvalid hearlier I (fun g hg => by
        obtain ⟨⟨_, hzL, _⟩, ⟨hop, hzM, hrest⟩⟩ := hI g hg
        exact ⟨hop, hzM, hzL, hrest⟩)
