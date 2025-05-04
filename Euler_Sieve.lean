import Mathlib

set_option maxHeartbeats 1000000

open Nat
open Classical
open List

@[simp]
def list_sorted : List Nat → Prop
| []      => True
| [_x]     => True
| x::y::l => x < y ∧ list_sorted (y::l)

lemma head_sorted_lowbound {x : ℕ} {l : List ℕ} (h : list_sorted (x :: l))
(z : ℕ) (hz : z ∈ x :: l) : x ≤ z := by
  induction l generalizing x with
  | nil => rw [List.mem_singleton] at hz; subst hz; apply Nat.le_refl
  | cons y ys ih =>
    rw [List.mem_cons] at hz
    obtain rfl | hz := hz
    · apply Nat.le_refl
    apply Nat.le_trans
    · exact Nat.le_of_lt h.left
    · exact ih h.right hz

def sorted_bounded_list (i j: Nat) : Type :=
  { ps : List Nat // list_sorted ps ∧ (∀ x ∈ ps, j ≤ x ∧ x ≤ i) }

def empty_sorted_bounded_list (i j: Nat) : sorted_bounded_list i j :=
  ⟨[], by simp, by simp⟩

def correct_PS : sorted_bounded_list i j → Prop :=
  fun ⟨ps, _h⟩ => ∀ x, j ≤ x ∧ x ≤ i → (x ∈ ps ↔ Nat.Prime x)

lemma empty_correct {i j : ℕ}(h : ∀ x, j ≤ x ∧ x ≤ i → ¬ Nat.Prime x)
  : correct_PS (empty_sorted_bounded_list i j) := by
  intros x hx
  constructor
  · simp
  · intro hp
    have hcontra: ¬Nat.Prime x := h x hx
    simp_all

def final_PS (i: Nat) : Type :=
  { ps : sorted_bounded_list i 2// correct_PS ps}

def final_FS (i n : Nat) : Type :=
  { f : Nat → Nat //
      (∀ m, ((f m = 0) ∨ (f m = Nat.minFac m))) ∧
      (∀ x, 2 ≤ x ∧ x ≤ i → f x = Nat.minFac x ∧
      ∀ y, (Nat.Prime y ∧ 2 ≤ y ∧ y ≤ f x) → x * y ≤ n → f (x * y) ≠ 0)}

-- key of the algorithm
lemma mul_of_least {p x : ℕ} (hp : Nat.Prime p) (hx : 2 ≤ x)
  (h : p ≤ Nat.minFac x) : Nat.minFac (p * x) = p := by
  have hl: Nat.minFac (p * x) ≤ p := by
    apply Nat.minFac_le_of_dvd
    apply Nat.Prime.two_le hp
    apply Nat.dvd_mul_right
  have hg: p ≤ Nat.minFac (p * x) := by
    let q := Nat.minFac (p * x)
    have hq_dvd : q ∣ p * x := by apply Nat.minFac_dvd
    have hq_nz : p*x ≠ 1 := by aesop
    have hq_prime : Nat.Prime q := Nat.minFac_prime hq_nz
    have hq_cases : (q ∣ p) ∨ (q ∣ x) := (Nat.Prime.dvd_mul hq_prime).mp hq_dvd
    match hq_cases with
    | Or.inl hqp =>
      have q_eq_p : q = p := (Nat.prime_dvd_prime_iff_eq hq_prime hp).mp hqp
      linarith
    | Or.inr hqx =>
      apply le_trans h (Nat.minFac_le_of_dvd (Nat.Prime.two_le hq_prime) hqx)
  linarith

lemma list_sorted_append (l : List Nat) (a : Nat)
  (h : list_sorted l) (H : ∀ x ∈ l, x < a) : list_sorted (l ++ [a]) := by
  induction l with
  | nil =>
    simp [list_sorted]
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp [list_sorted]
      aesop
    | cons hd2 tl2 =>
      simp [list_sorted] at h
      have h_hd : hd < hd2 := h.1
      have h_tl : list_sorted (hd2 :: tl2) := h.2
      have H' : ∀ x ∈ (hd2 :: tl2), x < a := by
        intros x hx
        apply H
        exact List.mem_cons_of_mem hd hx
      simp [list_sorted]
      exact ⟨h_hd, ih h_tl H'⟩

lemma list_sorted_tail (l : List Nat) (h : list_sorted l) : list_sorted l.tail := by
  induction l with
  | nil =>
    simp [list_sorted]
  | cons hd tl =>
    cases tl with
    | nil =>
      simp [list_sorted]
    | cons hd2 tl2 =>
      simp [list_sorted] at h
      simp [list_sorted]
      exact h.2

lemma tail_correct_PS {i j : ℕ} {ps : sorted_bounded_list i j}
  (H : correct_PS ps)
  {x y : ℕ} {l : List ℕ} (h : ps.1 = x :: y :: l) :
  list_sorted (y :: l) ∧ (∀ z, z ∈ (y :: l) → (x+1) ≤ z ∧ z ≤ i) ∧
    (∀ z, (x+1) ≤ z ∧ z ≤ i → (z ∈ (y :: l) ↔ Nat.Prime z)) := by
  have L_sorted : list_sorted (x :: y :: l) := h ▸ ps.2.1
  have sorted_tail : list_sorted (y :: l) := list_sorted_tail (x :: y :: l) L_sorted
  have bound_tail : ∀ z, z ∈ (y :: l) → (x+1) ≤ z ∧ z ≤ i := by
    intro z hz
    have h_zeq : z ∈ (y :: l) ↔ z ∈ (x :: y :: l) := by aesop
    constructor
    · have hzy: y ≤ z := head_sorted_lowbound sorted_tail z hz
      have hxy : x < y :=  by
        rcases L_sorted with ⟨hxy, _⟩
        apply hxy
      linarith
    · have hzps: z ∈ ps.1 := by
        rw[h]
        apply h_zeq.mp hz
      exact (ps.2.2 z hzps).right
  have equiv : ∀ z, (x+1) ≤ z ∧ z ≤ i → (z ∈ (y :: l) ↔ Nat.Prime z) := by
    intro z hz_bound
    have h_zeq : z ∈ (y :: l) ↔ z ∈ (x :: y :: l) := by aesop
    have H_equiv : z ∈ (x :: y :: l) ↔ Nat.Prime z := by
      have j_le_z : j ≤ z := by
        have hpsx: x∈ ps.1 := by aesop
        have hxj: j≤ x := (ps.2.2 x hpsx).1
        linarith
      have bound_z : j ≤ z ∧ z ≤ i := ⟨j_le_z, hz_bound.2⟩
      rcases ps with ⟨L, ⟨L_sorted, L_bound⟩⟩
      constructor
      · intro hzx
        have hzx' : z ∈ L := by aesop
        exact (H z bound_z).mp hzx'
      · intro p
        have hL : z ∈ L := (H z bound_z).mpr p
        aesop
    exact Iff.trans h_zeq H_equiv
  exact ⟨sorted_tail, bound_tail, equiv⟩

lemma no_primes_if_empty {i j : Nat} {ps : sorted_bounded_list i j}
  (H : correct_PS ps) (h_empty : ps.1 = []) :
  ∀ x, j ≤ x ∧ x ≤ i → ¬ Nat.Prime x := by
  intros x hx hprime
  specialize H x hx
  rw [h_empty] at H
  simp_all

lemma minFac_lt_lower_bound {i j : ℕ}
  (h : ∀ x, j ≤ x ∧ x ≤ i → ¬ Nat.Prime x) (hi : 2 ≤ i) :
  Nat.minFac i < j := by
  by_contra H'
  push_neg at H'
  have ni : i ≠ 1 := by nlinarith
  specialize h (Nat.minFac i)
  apply h
  constructor
  apply H'
  apply Nat.minFac_le
  linarith
  apply Nat.minFac_prime ni

-- simulate the update array in the sieve
def updateFunction (f : Nat → Nat) (k v : Nat) : Nat → Nat :=
  fun x => if x = k then v else f x

-- updateFunction preserves states
lemma updateFunction_preserves {f : Nat → Nat} {k v m : Nat} (h : m ≠ k) :
  updateFunction f k v m = f m := by
  simp [updateFunction]
  intro h'
  aesop

-- current i, sieve f, prime list ps, upper bound n
-- linear sieve by prime list
def processPrimes (i : Nat) (f : Nat → Nat) (ps : List Nat) (n : Nat): Nat → Nat :=
  match ps with
  | []         => f
  | p :: ps'   =>
    if p > f i ∨ i * p > n then f
    else
      let f' := updateFunction f (i * p) p
      processPrimes i f' ps' n

-- current i, prime list primes, sieve f
-- linear sieve from i to n
def EulerSieveAux (n i : Nat) (ps : List Nat) (f : Nat → Nat): (List Nat × (Nat → Nat)) :=
  if i > n then (ps, f)
  else
    let (ps', f') :=
      if f i = 0 then
        -- i is prime
        let fNew := updateFunction f i i
        (ps ++ [i], processPrimes i fNew (ps ++ [i]) n)
      else
        (ps, processPrimes i f ps n)
    EulerSieveAux n (i + 1) ps' f'
termination_by n + 1 - i

-- initial EulerSieve
def EulerSieve (n : Nat) : (List Nat × (Nat → Nat)) :=
  EulerSieveAux n 2 [] (fun _ => 0)

#eval (EulerSieve 20).1

def processPrimes_complete (n i j : Nat)(hi: 2 ≤ i)
  (ps : sorted_bounded_list (i+1) (j+1))(hps: correct_PS ps)(f : Nat → Nat)
  (hf₁ : ∀ m, (f m = 0) ∨ (f m = Nat.minFac m))
  (hf₂ : ∀ x, 2 ≤ x ∧ x ≤ i → f x = Nat.minFac x ∧ ∀ y, (Nat.Prime y ∧ 2 ≤ y ∧ y ≤ f x) → x * y ≤ n → f (x * y) ≠ 0)
  (hf₃ : f (i+1) = Nat.minFac (i+1))
  (hf₄ : ∀ a, (Nat.Prime a ∧ a ≤ j) → f ((i+1) * a) = Nat.minFac ((i+1) * a))
  (hf₅ : ∀ m, f m ≤ (i+1))
  : {F : final_FS (i+1) n // ∀ m, F.1 m ≤ (i+1)} :=
  match ps with
  | ⟨[], ps_props⟩ =>
    ⟨ ⟨ f, hf₁,
        fun x hx =>
          if h : x = i+1 then by
              have h_no_prime : ∀ z, (j+1) ≤ z ∧ z ≤ (i+1) → ¬ Nat.Prime z := by
                apply no_primes_if_empty hps
                rfl
              have h_min : Nat.minFac (i+1) < (j+1) :=
                minFac_lt_lower_bound h_no_prime (by linarith)
              constructor
              · aesop
              · intro y hy hxy
                have y_le : y ≤ f (i+1) := by aesop
                rw [hf₃] at y_le
                have y_le_j : y ≤ j := by linarith
                have hi: f ((i + 1) * y) = ((i + 1) * y).minFac := hf₄ y ⟨hy.1, y_le_j⟩
                rw[h,hi]
                apply pos_iff_ne_zero.mp
                apply Nat.minFac_pos
          else
              have Hx : 2 ≤ x ∧ x ≤ i := by
                constructor
                · apply hx.1
                · apply Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne hx.2 h)
              hf₂ x Hx
    ⟩ , hf₅⟩
  | ⟨[p], ps_props⟩ =>
      if hcond : p > f (i+1) ∨ (i+1) * p > n then
        ⟨ ⟨ f, hf₁,
          fun x hx =>
            if h : x = i+1 then by
              have fprime : Nat.Prime (f (i+1)) := by
                rw[hf₃]
                apply Nat.minFac_prime
                aesop
              have hi' : f (i+1) ≤ i+1 := by
                rw[hf₃]
                apply Nat.minFac_le
                norm_num
              constructor
              · aesop
              · intro y hy hxy
                have y_le : y ≤ f (i+1) := by aesop
                by_cases hp : p > f (i+1)
                · have hj : ¬ ((j+1) ≤ f (i+1)) := by
                    intro hj'
                    have bound : (j+1) ≤ f (i+1) ∧ f (i+1) ≤ (i+1) := ⟨hj', hi'⟩
                    have h_ps : f (i+1) ∈ [p] ↔ Nat.Prime (f (i+1)) := hps (f (i+1)) bound
                    have h_prime : Nat.Prime (f (i+1)) := fprime
                    have hcontra : f (i+1) ∈ [p] := h_ps.mpr h_prime
                    have hcontra' : f (i+1) = p := List.mem_singleton.mp hcontra
                    linarith
                  apply Nat.lt_of_not_le at hj
                  have hy': y ≤ j := by linarith
                  have hf4_applied : f ((i+1) * y) = ((i+1) * y).minFac := hf₄ y ⟨hy.1, hy'⟩
                  rw[← h] at hf4_applied
                  rw [hf4_applied]
                  have pos_minfac: 0 < (x * y).minFac := Nat.minFac_pos (x*y)
                  linarith
                · have hcond' : (i + 1) * p > n := Or.resolve_left hcond hp
                  have hyp: y < p := by nlinarith
                  have hyj: ¬ ((j+1) ≤ y) := by
                    intro hyj'
                    have hyi : y ≤ i + 1 := by
                      apply le_trans hy.2.2
                      rw[h]
                      apply hi'
                    have bound : (j+1) ≤ y ∧ y ≤ (i+1) := ⟨hyj', hyi⟩
                    have h_ps : y ∈ [p] ↔ Nat.Prime y := hps y bound
                    have h_prime : Nat.Prime y := hy.1
                    have hcontra : y ∈ [p] := h_ps.mpr h_prime
                    have hcontra' : y = p := List.mem_singleton.mp hcontra
                    linarith
                  apply Nat.lt_of_not_le at hyj
                  have hyj': y ≤ j := by linarith
                  have hf4_applied : f ((i+1) * y) = ((i+1) * y).minFac := hf₄ y ⟨hy.1, hyj'⟩
                  rw[← h] at hf4_applied
                  rw [hf4_applied]
                  have pos_minfac: 0 < (x * y).minFac := Nat.minFac_pos (x*y)
                  linarith
            else
              have Hx : 2 ≤ x ∧ x ≤ i := by
                constructor
                · apply hx.1
                · apply Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne hx.2 h)
              hf₂ x Hx
        ⟩,hf₅⟩
      else
        let f' := updateFunction f (p * (i+1)) p
        let ps' := empty_sorted_bounded_list (i+1) (p+1)
        have hp : Nat.Prime p := by
          have mem : p ∈ [p] := List.mem_singleton_self p
          have bound : (j+1) ≤ p ∧ p ≤ (i+1) := ps_props.2 p mem
          exact (hps p bound).mp mem
        have hps' : correct_PS ps' := by
          apply empty_correct
          intro x Hx hpx
          have bound : (j+1) ≤ x ∧ x ≤ (i+1) := by
            constructor
            · have hjp : (j+1) ≤ p := (ps_props.2 p (List.mem_singleton_self p)).1
              linarith
            · apply Hx.2
          have h_ps : x ∈ [p] ↔ Nat.Prime x := hps x bound
          have hcontra : x ∈ [p] := h_ps.mpr hpx
          have hcontra' : x = p := List.mem_singleton.mp hcontra
          linarith
        have hf₁' : ∀ m', (f' m' = 0) ∨ (f' m' = Nat.minFac m') := by
          intro m'
          by_cases h : m' = p * (i+1)
          · have hm: Nat.minFac m' = f' m' := by
              rw[h]
              simp [f', updateFunction]
              apply mul_of_least
              exact hp
              linarith
              aesop
            rw [hm]
            right
            rfl
          · simp [f']
            rw [updateFunction_preserves h]
            exact hf₁ m'
        have hf₂' : ∀ x', 2 ≤ x' ∧ x' ≤ i → f' x' = Nat.minFac x' ∧ ∀ y', (Nat.Prime y' ∧ 2 ≤ y' ∧ y' ≤ f' x') → x' * y' ≤ n → f' (x' * y') ≠ 0 := by
                  intro x hx
                  constructor
                  · have h_ne : x ≠ p * (i+1) := by
                      intro h_eq
                      have h_lower_bound : (i+1) * 2 ≤ (i+1) * p := by
                        apply Nat.mul_le_mul_left
                        apply Nat.Prime.two_le hp
                      have h_gt : 2 * (i+1) > i := by
                        calc
                          2 * (i+1) = 2 * i + 2 := by ring
                          _ > i         := by linarith
                      linarith
                    simp [f']
                    rw [updateFunction_preserves h_ne]
                    exact (hf₂ x hx).1
                  · intro y hy hxy
                    have hx_ne : x ≠ p * (i+1) := by
                      intro h_eq
                      have h_lower_bound : 2 * (i+1) ≤ p * (i+1) := Nat.mul_le_mul_right (i+1) (Nat.Prime.two_le hp)
                      have h_gt : 2 * (i+1) > i+1 := by linarith
                      have h_contr : p * (i+1) > i+1 := by linarith [h_lower_bound, h_gt]
                      have h_bound : x ≤ i := hx.2
                      linarith
                    have hfx: f' x = f x := by
                      simp [f']
                      rw [updateFunction_preserves hx_ne]
                    have hy': Nat.Prime y ∧ 2 ≤ y ∧ y ≤ f x := by aesop
                    have h_ne : x * y ≠ p * (i+1) := by
                      intro h_eq
                      have dvd_xy : p ∣ x * y := by
                        rw [h_eq]
                        apply Nat.dvd_mul_right _ _
                      cases (Nat.Prime.dvd_mul hp).mp dvd_xy with
                      | inl hpx =>
                        obtain ⟨k, hk⟩ :=exists_eq_mul_right_of_dvd hpx
                        rw [hk,mul_assoc] at h_eq
                        have h1 : k * y = i + 1 := (Nat.mul_right_inj (pos_iff_ne_zero.mp (Nat.Prime.pos hp))).mp h_eq
                        have y_le_p : y ≤ p := by
                          have fx_le_p : f x ≤ p:= by
                            rw[(hf₂ x hx).1]
                            apply Nat.minFac_le_of_dvd (Nat.Prime.two_le hp) hpx
                          linarith
                        have h2 : k * y ≤ k * p := Nat.mul_le_mul_left k y_le_p
                        linarith
                      | inr hpy =>
                        have hy_eq : p = y := (Nat.prime_dvd_prime_iff_eq hp hy.1).mp hpy
                        rw [hy_eq, mul_comm] at h_eq
                        have h_x : x = i + 1 := Nat.mul_left_cancel (Nat.Prime.pos hy.1) h_eq
                        linarith
                    simp [f']
                    rw [updateFunction_preserves h_ne]
                    exact (hf₂ x hx).2 y hy' hxy
        have hf₃' : f' (i+1) = Nat.minFac (i+1) := by
          have hm': (i+1) ≠ p * (i+1) := by
            intro hip
            have hp1 : 1 < p := Nat.Prime.one_lt hp
            have i_pos : 0 < i + 1 := by norm_num
            have hmul : (i + 1) * 1 < (i + 1) * p := mul_lt_mul_of_pos_left hp1 i_pos
            linarith
          simp [f']
          rw [updateFunction_preserves hm']
          exact hf₃
        have hf₄' : ∀ a', (Nat.Prime a' ∧ a' ≤ p) → f' ((i+1) * a') = Nat.minFac ((i+1) * a') := by
          intro a ha
          by_cases hap : a = p
          · rw[hap]
            simp [f', updateFunction, Nat.mul_comm]
            symm
            apply mul_of_least
            exact hp
            linarith
            aesop
          · have hap': a < p := lt_iff_le_and_ne.mpr ⟨ha.2, hap⟩
            have haj: ¬ (a ≥ (j+1)):= by
              intro haj'
              have bound : (j+1) ≤ a ∧ a ≤ (i+1) := by
                constructor
                · apply haj'
                · have mem_p : p ∈ [p] := List.mem_singleton_self p
                  have bound_p : (j+1) ≤ p ∧ p ≤ (i+1) := ps_props.2 p mem_p
                  apply Nat.le_trans ha.2 bound_p.2
              have h_ps : a ∈ [p] ↔ Nat.Prime a := hps a bound
              have hcontra : a ∈ [p] := h_ps.mpr ha.1
              have hcontra' : a = p := List.mem_singleton.mp hcontra
              linarith
            have haj' : a < j + 1 := Nat.lt_of_not_ge haj
            rw [Nat.lt_succ_iff] at haj'
            have hai: (i + 1) * a ≠ p * (i+1) := by
              intro h_eq
              rw [mul_comm] at h_eq
              have : a = p := Nat.mul_right_cancel (Nat.succ_pos i) h_eq
              linarith
            simp [f']
            rw [updateFunction_preserves hai]
            apply hf₄ a ⟨ ha.1, haj' ⟩
        have hf₅': ∀ m', f' m' ≤ (i+1):= by
          intro m
          by_cases hm': m ≠ p * (i+1)
          · simp [f']
            rw [updateFunction_preserves hm']
            apply hf₅
          · simp [f']
            simp at hm'
            rw[hm']
            simp [updateFunction]
            have hpin: p ∈ [p] := by aesop
            exact (ps_props.2 p hpin).2
        processPrimes_complete n i p hi ps' hps' f' hf₁' hf₂' hf₃' hf₄' hf₅'
  | ⟨ p :: q :: ps', ps_props⟩ =>
    if hcond : p > f (i+1) ∨ (i+1) * p > n then
      ⟨ ⟨ f, hf₁,
        fun x hx =>
          if h : x = i+1 then by
            have fprime : Nat.Prime (f (i+1)) := by
              rw [hf₃]
              apply Nat.minFac_prime
              aesop
            have hi' : f (i+1) ≤ i+1 := by
              rw [hf₃]
              apply Nat.minFac_le
              norm_num
            constructor
            · rw [h, hf₃]
            · intro y hy hxy
              have y_le : y ≤ f (i+1) := by aesop
              by_cases hp : p > f (i+1)
              · have hj : ¬ ((j+1) ≤ f (i+1)) := by
                  intro hj'
                  let bound : (j+1) ≤ f (i+1) ∧ f (i+1) ≤ (i+1) := ⟨hj', hi'⟩
                  have h_ps : f (i+1) ∈ (p :: q :: ps') ↔ Nat.Prime (f (i+1)) := hps (f (i+1)) bound
                  have fprime' : Nat.Prime (f (i+1)) := fprime
                  have hcontra : f (i+1) ∈ (p :: q :: ps') := h_ps.mpr fprime'
                  have hmin : p ≤ f (i+1) := head_sorted_lowbound ps_props.1 (f (i+1)) hcontra
                  linarith
                apply Nat.lt_of_not_le at hj
                have hy' : y ≤ j := by linarith
                have hf4_applied : f ((i+1) * y) = ((i+1) * y).minFac := hf₄ y ⟨hy.1, hy'⟩
                rw [← h] at hf4_applied
                rw [hf4_applied]
                have pos_minfac: 0 < (x * y).minFac := Nat.minFac_pos (x*y)
                linarith
              · have hcond' : (i+1) * p > n := Or.resolve_left hcond hp
                have hyp : y < p := by nlinarith
                have hyj : ¬ ((j+1) ≤ y) := by
                  intro hyj'
                  have hyi : y ≤ i+1 := by
                    apply le_trans hy.2.2
                    rw [h]
                    exact hi'
                  have bound : (j+1) ≤ y ∧ y ≤ (i+1) := ⟨hyj', hyi⟩
                  have h_ps : y ∈ (p :: q :: ps') ↔ Nat.Prime y := hps y bound
                  have h_prime : Nat.Prime y := hy.1
                  have hcontra : y ∈ (p :: q :: ps') := h_ps.mpr h_prime
                  have min_y : p ≤ y := head_sorted_lowbound ps_props.1 y hcontra
                  linarith
                apply Nat.lt_of_not_le at hyj
                have hyj' : y ≤ j := by linarith
                have hf4_applied : f ((i+1) * y) = ((i+1) * y).minFac := hf₄ y ⟨hy.1, hyj'⟩
                rw [← h] at hf4_applied
                rw [hf4_applied]
                have pos_minfac: 0 < (x * y).minFac := Nat.minFac_pos (x*y)
                linarith
          else
            have Hx : 2 ≤ x ∧ x ≤ i := by
                constructor
                · apply hx.1
                · apply Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne hx.2 h)
            hf₂ x Hx
      ⟩,hf₅⟩
    else
      let f' := updateFunction f (p * (i+1)) p
      let ps_new : sorted_bounded_list (i+1) (p+1) := ⟨ q :: ps', list_sorted_tail (p :: q :: ps') ps_props.1,
        by
        intros x hx
        have x_in_all : x ∈ (p :: q :: ps') := by simp [hx]
        have x_upper : x ≤ i+1 := (ps_props.2 x x_in_all).2
        have p_lt_q : p < q := (ps_props.1).1
        have q_le_x : q ≤ x := head_sorted_lowbound (list_sorted_tail (p :: q :: ps') ps_props.1) x hx
        have p1_le_q : p+1 ≤ q := Nat.succ_le_of_lt p_lt_q
        exact ⟨Nat.le_trans p1_le_q q_le_x, x_upper⟩
        ⟩
      have hp : Nat.Prime p := by
        have mem : p ∈ (p :: q :: ps') := by aesop
        have bound : (j+1) ≤ p ∧ p ≤ (i+1) := ps_props.2 p mem
        exact (hps p bound).mp mem
      have hps' : correct_PS ps_new := (tail_correct_PS hps rfl).2.2
      have hf₁' : ∀ m', (f' m' = 0) ∨ (f' m' = Nat.minFac m') := by
        intro m'
        by_cases h : m' = p * (i+1)
        · have hm: Nat.minFac m' = f' m' := by
            rw[h]
            simp [f', updateFunction]
            apply mul_of_least
            apply hp
            linarith
            aesop
          rw [hm]
          right
          rfl
        · simp [f']
          rw [updateFunction_preserves h]
          exact hf₁ m'
      have hf₂' : ∀ x', 2 ≤ x' ∧ x' ≤ i → f' x' = Nat.minFac x' ∧ ∀ y', (Nat.Prime y' ∧ 2 ≤ y' ∧ y' ≤ f' x') → x' * y' ≤ n → f' (x' * y') ≠ 0 := by
        intro x hx
        constructor
        · have h_ne : x ≠ p * (i+1) :=
            by
              intro h_eq
              have lower_bound : (i+1) * 2 ≤ (i+1) * p :=
                Nat.mul_le_mul_left (i+1) (Nat.Prime.two_le hp)
              have gt_bound : 2 * (i+1) > i :=
                by
                  calc
                    2 * (i+1) = 2 * i + 2 := by ring
                    _ > i         := by linarith
              linarith
          simp [f']
          rw [updateFunction_preserves h_ne]
          exact (hf₂ x hx).1
        · intro y hy hxy
          have hx_ne : x ≠ p * (i+1) := by
            intro h_eq
            have lower_bound : (i+1) * 2 ≤ (i+1) * p := Nat.mul_le_mul_left (i+1) (Nat.Prime.two_le hp)
            have gt_bound : 2 * (i+1) > i+1 := by linarith
            linarith
          have hfx : f' x = f x := by
            simp [f']
            rw [updateFunction_preserves hx_ne]
          have hy' : Nat.Prime y ∧ 2 ≤ y ∧ y ≤ f x := by
            constructor
            · apply hy.1
            · constructor
              · apply hy.2.1
              · rw[← hfx]
                apply hy.2.2
          have h_mul_ne : x * y ≠ p * (i+1) :=by
              intro h_eq
              have dvd_xy : p ∣ x * y :=
                by
                  rw [h_eq]
                  apply Nat.dvd_mul_right
              cases (Nat.Prime.dvd_mul hp).mp dvd_xy with
              | inl hpx =>
                obtain ⟨k, hk⟩ := exists_eq_mul_right_of_dvd hpx
                rw [hk, mul_assoc] at h_eq
                have h1 : k * y = i+1 :=
                  (Nat.mul_right_inj (pos_iff_ne_zero.mp (Nat.Prime.pos hp))).mp h_eq
                have fx_le_p : f x ≤ p := by
                  rw [(hf₂ x hx).1]
                  apply Nat.minFac_le_of_dvd (Nat.Prime.two_le hp) hpx
                have y_le_p : y ≤ p := by
                  rw [hfx] at hy
                  linarith
                have h2 : k * y ≤ k * p := Nat.mul_le_mul_left k y_le_p
                linarith
              | inr hpy =>
                let hy_eq := (Nat.prime_dvd_prime_iff_eq hp hy.1).mp hpy
                rw [hy_eq, mul_comm] at h_eq
                have h_x : x = i+1 :=
                  Nat.mul_left_cancel (Nat.Prime.pos hy.1) h_eq
                linarith
          simp [f']
          rw [updateFunction_preserves h_mul_ne]
          exact (hf₂ x hx).2 y hy' hxy
      have hf₃' : f' (i+1) = Nat.minFac (i+1) := by
        have hm': (i+1) ≠ p * (i+1) := by
          intro hip
          have hp1 : 1 < p := Nat.Prime.one_lt hp
          have i_pos : 0 < i + 1 := by norm_num
          have hmul : (i + 1) * 1 < (i + 1) * p := mul_lt_mul_of_pos_left hp1 i_pos
          linarith
        simp [f']
        rw [updateFunction_preserves hm']
        exact hf₃
      have hf₄' : ∀ a', (Nat.Prime a' ∧ a' ≤ p) → f' ((i+1) * a') = Nat.minFac ((i+1) * a') := by
        intro a ha
        by_cases hap : a = p
        · rw [hap]
          simp [f', updateFunction, Nat.mul_comm]
          symm
          apply mul_of_least
          exact hp
          linarith
          aesop
        · have hap' : a < p := lt_iff_le_and_ne.mpr ⟨ha.2, hap⟩
          have haj : ¬ (a ≥ (j+1)) := by
            intro H
            have bound_a : (j+1) ≤ a ∧ a ≤ (i+1) := by
              constructor
              · exact H
              · have mem_p : p ∈ (p :: q :: ps') := by aesop
                have bound_p : (j+1) ≤ p ∧ p ≤ (i+1) := ps_props.2 p mem_p
                exact Nat.le_trans ha.2 bound_p.2
            have a_in_ps : a ∈ (p :: q :: ps') := (hps a bound_a).mpr ha.1
            have h_le : p ≤ a := head_sorted_lowbound ps_props.1 a a_in_ps
            linarith
          have haj' : a < j + 1 := Nat.lt_of_not_ge haj
          rw [Nat.lt_succ_iff] at haj'
          have hai : (i + 1) * a ≠ p * (i+1) := by
            intro h_eq
            rw [mul_comm] at h_eq
            have : a = p := Nat.mul_right_cancel (Nat.succ_pos i) h_eq
            linarith
          simp [f']
          rw [updateFunction_preserves hai]
          apply hf₄ a ⟨ ha.1, haj' ⟩
      have hf₅': ∀ m', f' m' ≤ (i+1):= by
          intro m
          by_cases hm': m ≠ p * (i+1)
          · simp [f']
            rw [updateFunction_preserves hm']
            apply hf₅
          · simp [f']
            simp at hm'
            rw[hm']
            simp [updateFunction]
            have hpin: p ∈ (p :: q :: ps') := by aesop
            exact (ps_props.2 p hpin).2
      processPrimes_complete n i p hi ps_new hps' f' hf₁' hf₂' hf₃' hf₄' hf₅'
  termination_by ps.1.length
  decreasing_by
    · have h_empty: (empty_sorted_bounded_list (i + 1) (p + 1)).1 = [] := by rfl
      rw[h_empty]
      simp
    · simp

def EulerSieveAux_complete (n i: Nat)(hi: 2 ≤ i)(hin: i ≤ n)
(PS : final_PS i) (F : final_FS i n) (hF: ∀ m, F.1 m ≤ i): (final_PS n) × (final_FS n n) :=
  if h : i = n then by
    subst h
    exact (PS, F)
  else
    have hi' : 2 ≤ i+1 := by linarith
    have hi'n : i+1 ≤ n := lt_iff_le_and_ne.mpr ⟨hin, h⟩
    if hval : F.val (i+1) = 0 then by
      let ⟨⟨ps, psProp1⟩, psProp2⟩ := PS
      let ⟨f, fProp⟩ := F
      let newList := ps ++ [i+1]
      let newF := updateFunction f (i+1) (i+1)
      have newList_sorted : list_sorted newList := by
        apply list_sorted_append
        apply psProp1.1
        intro x hxps
        have hxi: x ≤ i := (psProp1.2 x hxps).2
        linarith
      have newList_bounded : ∀ x, x ∈ newList → 2 ≤ x ∧ x ≤ (i + 1) := by
        intro x hxnl
        cases List.mem_append.1 hxnl with
        | inl hps =>
          have ⟨hx2, hxi⟩ := psProp1.2 x hps
          exact ⟨hx2, Nat.le_trans hxi (Nat.le_succ i)⟩
        | inr htail =>
          rw [List.mem_singleton] at htail
          aesop
      have hPi: Nat.Prime (i+1) := by
        have hfac: ∀ x, 2 ≤ x → x < (i+1) → ¬ (x∣(i + 1)) := by
          intro x hx₁ hx₂ hxdvd
          have hinP: ¬ (Nat.Prime (i + 1)) := by
            intro hprime
            have hcontra: i+1 = x := (Nat.Prime.dvd_iff_eq hprime (by linarith)).mp hxdvd
            linarith
          have hxlf: Nat.minFac (i + 1) < (i + 1) := (Nat.not_prime_iff_minFac_lt (by linarith)).mp hinP
          let k := (i + 1)/Nat.minFac (i + 1)
          have k_eq : k = (i+1) / (i+1).minFac := by aesop
          have hk: Nat.minFac (i + 1) ≤ k := Nat.minFac_le_div (by linarith) hinP
          have hf_contra: f (i + 1) ≠ 0 := by
            have hik: k * Nat.minFac (i + 1) = i + 1:= by
              simp [k]
              apply Nat.div_mul_cancel
              apply Nat.minFac_dvd (i+1)
            have hfacP: Nat.Prime (Nat.minFac (i + 1)) := Nat.minFac_prime (by linarith)
            have h2lefac : 2 ≤ Nat.minFac (i + 1) := Nat.Prime.two_le hfacP
            have hk_bound: 2 ≤ k ∧ k ≤ i := by
              constructor
              · exact le_trans h2lefac hk
              · have k_le : (i+1) / (i+1).minFac ≤ (i+1) / 2 :=
                  Nat.div_le_div_left h2lefac (by norm_num)
                have half_bound : (i+1) / 2 ≤ i := by
                  apply Nat.div_le_of_le_mul
                  linarith
                rw [k_eq]
                exact le_trans k_le half_bound
            have hk_ge: Nat.minFac (i + 1) ≤ f k := by
              have eq_fk := (fProp.2 k hk_bound).1
              rw [eq_fk]
              by_contra hContr
              push_neg at hContr
              let p := Nat.minFac k
              have p_prime : Nat.Prime p := Nat.minFac_prime (by aesop)
              have p_dvd_k : p ∣ k := Nat.minFac_dvd k
              have p_dvd_i1 : p ∣ (i + 1) := by
                rw[← hik]
                apply dvd_mul_of_dvd_left p_dvd_k (i+1).minFac
              have h_ilep: (i + 1).minFac ≤ p := Nat.minFac_le_of_dvd (Nat.Prime.two_le p_prime) p_dvd_i1
              linarith
            rw[← hik]
            apply (fProp.2 k hk_bound).2 (Nat.minFac (i + 1)) ⟨hfacP, h2lefac, hk_ge⟩ (by rw[hik]; apply hi'n)
          simp at hval
          apply hf_contra hval
        apply Nat.prime_def_lt'.mpr ⟨ (by linarith), hfac ⟩
      have hps : correct_PS ⟨ newList, newList_sorted, newList_bounded ⟩ := by
        simp [correct_PS]
        intro x hx₁ hx₂
        constructor
        · intro hmem
          cases List.mem_append.1 hmem with
          | inl h_in_ps =>
            have h_bound_ps : 2 ≤ x ∧ x ≤ i := psProp1.2 x h_in_ps
            apply (psProp2 x h_bound_ps).mp h_in_ps
          | inr h_eq =>
            have hxi: x = i+1 := by aesop
            rw [hxi]
            exact hPi
        · intro hprime
          by_cases h_case : x = i+1
          · rw [h_case]
            exact List.mem_append_right _ (List.mem_singleton_self (i+1))
          · have h_lt : x < i+1 := lt_of_le_of_ne hx₂ h_case
            have h_le_i : x ≤ i := Nat.le_of_lt_succ h_lt
            have h_equiv := psProp2 x ⟨hx₁, h_le_i⟩
            exact List.mem_append_left _ (h_equiv.mpr hprime)
      have hf₃ : newF (i+1) = Nat.minFac (i+1) := by
        have hFi: newF (i+1) = (i+1) := by simp [newF,updateFunction]
        rw[hFi]
        symm
        apply Nat.Prime.minFac_eq hPi
      have hf₁ : ∀ m, (newF m = 0) ∨ (newF m = Nat.minFac m) := by
        intro m
        by_cases hmi: m = i+1
        · simp_all
        · simp [newF,updateFunction]
          rw [if_neg hmi]
          apply fProp.1 m
      have hf₂ : ∀ x, 2 ≤ x ∧ x ≤ i → newF x = Nat.minFac x ∧ ∀ y, (Nat.Prime y ∧ 2 ≤ y ∧ y ≤ newF x) → x * y ≤ n → newF (x * y) ≠ 0 := by
        intro x hx
        have hxnei: x ≠ (i+1) := by aesop
        simp [newF,updateFunction]
        rw [if_neg hxnei]
        aesop
      have hf₄ : ∀ a, (Nat.Prime a ∧ a ≤ 1) → newF ((i+1) * a) = Nat.minFac ((i+1) * a) := by
        intro a ha
        have ha': 1 < a := Nat.Prime.one_lt ha.1
        have h_contra : a < a := lt_of_le_of_lt ha.2 ha'
        linarith
      have hf₅: ∀ m', newF m' ≤ (i+1) := by
        intro m
        by_cases hmi: m = i+1
        · simp_all
        · simp [newF,updateFunction]
          rw [if_neg hmi]
          have hFmi : f m ≤ i := hF m
          linarith
      let F' := processPrimes_complete n i 1 hi ⟨ newList, newList_sorted, newList_bounded ⟩ hps newF hf₁ hf₂ hf₃ hf₄ hf₅
      exact EulerSieveAux_complete n (i+1) hi' hi'n ⟨⟨ newList, newList_sorted, newList_bounded ⟩,hps⟩ F'.1 F'.2
    else by
      let ⟨⟨ps, psProp1⟩, psProp2⟩ := PS
      let ⟨f, fProp⟩ := F
      have newList_bounded : ∀ x, x ∈ ps → 2 ≤ x ∧ x ≤ (i+1) := by
        intro x hx
        have hxi: x ≤ i:= (psProp1.2 x hx).2
        constructor
        · apply (psProp1.2 x hx).1
        · linarith
      let psNew : sorted_bounded_list (i+1) 2 := ⟨ ps, psProp1.1, newList_bounded ⟩
      have hps : correct_PS psNew := by
        intros x hx
        by_cases hxi': x = i+1
        · constructor
          · intro hxps
            have hxi: x ≤ i := (psProp1.2 x hxps).2
            linarith
          · intro hxp
            have hval' : ¬ (f x = 0) := by aesop
            have hxfac: x.minFac ≤ i := by
              have hfx: f x = x.minFac := (or_iff_not_imp_left.mp (fProp.1 x)) hval'
              have hxi: f x ≤ i := hF x
              linarith
            have hxlf: x.minFac = x := Nat.Prime.minFac_eq hxp
            linarith
        · have hxi : x ≤ i := by
            have hxi : x < i + 1 := Nat.lt_of_le_of_ne hx.2 hxi'
            exact Nat.lt_succ_iff.mp hxi
          have hx_bound : 2 ≤ x ∧ x ≤ i := ⟨ hx.1, hxi⟩
          apply psProp2 x hx_bound
      have hf₃ : f (i+1) = Nat.minFac (i+1) := Or.resolve_left (fProp.1 (i+1)) hval
      have hf₄ : ∀ a, (Nat.Prime a ∧ a ≤ 1) → f ((i+1) * a) = Nat.minFac ((i+1) * a) := by
        intro a ha
        have ha': 1 < a := Nat.Prime.one_lt ha.1
        have h_contra : a < a := lt_of_le_of_lt ha.2 ha'
        linarith
      have hf₅: ∀ m, f m ≤ (i+1) := by
        intro m
        apply le_trans (hF m)
        norm_num
      let F' := processPrimes_complete n i 1 hi psNew hps f fProp.1 fProp.2 hf₃ hf₄ hf₅
      exact EulerSieveAux_complete n (i+1) hi' hi'n ⟨psNew,hps⟩ F'.1 F'.2
termination_by n-i

def EulerSieve_complete (n : Nat) (hn : 2 ≤ n) : final_PS n × final_FS n n :=
  let PS_init : final_PS 2 :=
    ⟨ ⟨[2],
        by simp [list_sorted],
        by
          intros x hx
          have xval: x=2:= List.mem_singleton.mp hx
          aesop⟩,
      by
        intros x hx
        constructor
        · intro hxval
          have xval: x=2:= List.mem_singleton.mp hxval
          rw[xval]
          apply Nat.prime_two
        · intro hxP
          have xval: x=2:= by linarith
          rw[xval]
          apply List.mem_singleton_self 2
        ⟩
  let f := updateFunction (updateFunction (fun _ => 0) 2 2) 4 2
  let F_init : final_FS 2 n :=
    ⟨ f ,
      by
        intro m
        simp [f, processPrimes, updateFunction]
        split_ifs with h4 h2
        · right
          rw[h4]
          aesop
        · right
          rw[h2]
          aesop
        · left
          rfl,
      by
        intros x hx
        have xval: x=2:= by linarith
        constructor
        · simp[f,updateFunction]
          rw[if_pos xval,xval,Nat.Prime.minFac_eq Nat.prime_two]
          simp
        · intro y
          simp[f,updateFunction]
          rw[if_pos xval]
          intros hy₁ hy₂ hy₃ hy₄
          simp at hy₃
          have yval: y=2:= by linarith
          rw[xval,yval]
          norm_num⟩
  EulerSieveAux_complete n 2 (by norm_num) hn PS_init F_init (
    by
    intro m
    simp [F_init, f, updateFunction]
    by_cases hm4 : m = 4
    · rw [if_pos hm4]
    · rw [if_neg hm4]
      by_cases hm2 : m = 2
      · rw [if_pos hm2]
      · rw [if_neg hm2]
        exact Nat.zero_le 2)

#eval (EulerSieve_complete 20 (by norm_num)).1.1.1
