import Calderon.EnergyBridge
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Sqrt

noncomputable section
set_option autoImplicit false
open Set Metric
open scoped BigOperators
namespace OAI.AnisotropicCalderon.Regularity

theorem exists_finite_half_open_cube_partition (B : ℝ) (hB : 0 < B) :
    let G_B : ℕ := Nat.ceil ((2 * B + 4) ^ 3)
    ∀ n : ℕ, 1 ≤ n →
    ∀ S : Set R3, S ⊆ ball (0 : R3) B →
    let cell : (Fin 3 → ℤ) → Set R3 := fun nu =>
      S ∩ {x : R3 | ∀ i : Fin 3,
        (nu i : ℝ) / (n : ℝ) ≤ x i ∧
        x i < ((nu i : ℝ) + 1) / (n : ℝ)}
    ∃ I : Finset (Fin 3 → ℤ),
    ∃ center : {nu : Fin 3 → ℤ // nu ∈ I} → R3,
      (∀ nu : Fin 3 → ℤ, nu ∈ I ↔ (cell nu).Nonempty) ∧
      (∀ nu : {nu : Fin 3 → ℤ // nu ∈ I}, center nu ∈ cell nu.1) ∧
      (S = ⋃ nu ∈ (I : Set (Fin 3 → ℤ)), cell nu) ∧
      (∀ nu ∈ I, ∀ mu ∈ I, nu ≠ mu → Disjoint (cell nu) (cell mu)) ∧
      (IsOpen S → ∀ nu : Fin 3 → ℤ, MeasurableSet (cell nu)) ∧
      (∀ nu ∈ I, ∀ x ∈ cell nu, ∀ y ∈ cell nu,
        dist x y ≤ Real.sqrt 3 / (n : ℝ)) ∧
      I.card ≤ G_B * n ^ 3 ∧
      ∀ (D : Set R3) (d : ℝ), 0 < d →
        (∀ z ∈ closure S, closedBall z (2 * d) ⊆ D) →
        ∀ nu : {nu : Fin 3 → ℤ // nu ∈ I},
          closedBall (center nu) (2 * d) ⊆ D := by
  classical
  dsimp only
  intro n hn S hSB
  -- G0/G1: the exact mesh has a positive denominator, including n = 1.
  have hN : 0 < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
  have hNOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  let cell : (Fin 3 → ℤ) → Set R3 := fun nu =>
    S ∩ {x : R3 | ∀ i : Fin 3,
      (nu i : ℝ) / (n : ℝ) ≤ x i ∧
      x i < ((nu i : ℝ) + 1) / (n : ℝ)}
  let a : ℤ := Int.floor (-B * (n : ℝ))
  let b : ℤ := Int.floor (B * (n : ℝ))
  let Q : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc a b)
  let I : Finset (Fin 3 → ℤ) := Q.filter (fun nu => (cell nu).Nonempty)
  have hAB : a ≤ b :=
    Int.floor_mono (by nlinarith only [mul_pos hB hN])
  -- G2: membership in a cell forces the unique floor label, on every face.
  have hLabel (nu : Fin 3 → ℤ) (x : R3) (hx : x ∈ cell nu) :
      (fun i : Fin 3 => Int.floor ((n : ℝ) * x i)) = nu := by
    funext i
    apply Int.floor_eq_iff.mpr
    constructor
    · simpa only [mul_comm] using (div_le_iff₀ hN).mp (hx.2 i).1
    · simpa only [mul_comm] using (lt_div_iff₀ hN).mp (hx.2 i).2
  have hPointQ (x : R3) (hx : x ∈ S) :
      (fun i : Fin 3 => Int.floor ((n : ℝ) * x i)) ∈ Q := by
    apply Fintype.mem_piFinset.mpr
    intro i
    have hAbs : |x i| < B :=
      (show |x i| ≤ ‖x‖ from by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i).trans_lt
          (mem_ball_zero_iff.mp (hSB hx))
    have hBounds : -B < x i ∧ x i < B := abs_lt.mp hAbs
    have hLo : -B * (n : ℝ) ≤ (n : ℝ) * x i := by
      nlinarith only [mul_le_mul_of_nonneg_left hBounds.1.le hN.le]
    have hHi : (n : ℝ) * x i ≤ B * (n : ℝ) := by
      nlinarith only [mul_le_mul_of_nonneg_left hBounds.2.le hN.le]
    exact Finset.mem_Icc.mpr ⟨Int.floor_mono hLo, Int.floor_mono hHi⟩
  have hPointCell (x : R3) (hx : x ∈ S) :
      x ∈ cell (fun i : Fin 3 => Int.floor ((n : ℝ) * x i)) := by
    refine ⟨hx, fun i => ?_⟩
    constructor
    · apply (div_le_iff₀ hN).mpr
      simpa only [mul_comm] using Int.floor_le ((n : ℝ) * x i)
    · apply (lt_div_iff₀ hN).mpr
      simpa only [mul_comm] using Int.lt_floor_add_one ((n : ℝ) * x i)
  have hActive (nu : Fin 3 → ℤ) : nu ∈ I ↔ (cell nu).Nonempty := by
    constructor
    · intro hnu
      exact (Finset.mem_filter.mp hnu).2
    · rintro ⟨x, hx⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, ⟨x, hx⟩⟩
      rw [← hLabel nu x hx]
      exact hPointQ x hx.1
  -- G0/G3: choose actual nonempty-cell centers, before any function or D/d caller.
  have hCenterExists (nu : {nu : Fin 3 → ℤ // nu ∈ I}) : (cell nu.1).Nonempty :=
    (hActive nu.1).mp nu.2
  choose center hCenter using hCenterExists
  refine ⟨I, center, hActive, hCenter, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- G3: this is a pointwise exact union, not an AE partition.
  · ext x
    constructor
    · intro hx
      let nu : Fin 3 → ℤ := fun i => Int.floor ((n : ℝ) * x i)
      have hxCell : x ∈ cell nu := hPointCell x hx
      have hnu : nu ∈ I := (hActive nu).mpr ⟨x, hxCell⟩
      exact mem_iUnion.mpr ⟨nu, mem_iUnion.mpr ⟨hnu, hxCell⟩⟩
    · intro hx
      obtain ⟨nu, hnu⟩ := mem_iUnion.mp hx
      obtain ⟨_hnuI, hxCell⟩ := mem_iUnion.mp hnu
      exact hxCell.1
  · intro nu _hnu mu _hmu hne
    apply Set.disjoint_left.mpr
    intro x hxNu hxMu
    apply hne
    exact (hLabel nu x hxNu).symm.trans (hLabel mu x hxMu)
  -- G4: conditional measurability uses precisely three coordinate Ico preimages.
  · intro hS nu
    change MeasurableSet (S ∩ {x : R3 | ∀ i : Fin 3,
      (nu i : ℝ) / (n : ℝ) ≤ x i ∧ x i < ((nu i : ℝ) + 1) / (n : ℝ)})
    apply hS.measurableSet.inter
    have hEach (i : Fin 3) :
        MeasurableSet ((fun x : R3 => x i) ⁻¹'
          Ico ((nu i : ℝ) / (n : ℝ)) (((nu i : ℝ) + 1) / (n : ℝ))) :=
      measurableSet_Ico.preimage (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).measurable
    convert MeasurableSet.iInter hEach using 1
    ext x
    simp only [mem_setOf_eq, mem_iInter, mem_preimage, mem_Ico]
  -- G7: compare canonical Euclidean squares, without a change of norm.
  · intro nu _hnu x hx y hy
    have hCoord (i : Fin 3) : |x i - y i| ≤ (1 : ℝ) / (n : ℝ) := by
      have hxLo := (hx.2 i).1
      have hxHi := (hx.2 i).2
      have hyLo := (hy.2 i).1
      have hyHi := (hy.2 i).2
      have hLength : ((nu i : ℝ) + 1) / (n : ℝ) - (nu i : ℝ) / (n : ℝ) =
          (1 : ℝ) / (n : ℝ) := by
        rw [← sub_div, add_sub_cancel_left]
      apply le_of_lt
      apply abs_lt.mpr
      constructor
      · linarith only [hyHi, hxLo, hLength]
      · linarith only [hxHi, hyLo, hLength]
    have hSqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hSq : ‖x - y‖ ^ 2 ≤ (Real.sqrt 3 / (n : ℝ)) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc
        (∑ i : Fin 3, ((x - y) i) ^ 2) ≤
            ∑ _i : Fin 3, ((1 : ℝ) / (n : ℝ)) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _hi
          rw [PiLp.sub_apply]
          simpa only [sq_abs] using
            (sq_le_sq₀ (abs_nonneg (x i - y i)) (div_nonneg zero_le_one hN.le)).mpr (hCoord i)
        _ = (3 : ℝ) * ((1 : ℝ) / (n : ℝ)) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_ofNat]
        _ = (Real.sqrt 3 / (n : ℝ)) ^ 2 := by
          simp only [div_pow, hSqrt, one_pow, mul_one_div]
    simpa only [dist_eq_norm] using
      (sq_le_sq₀ (norm_nonneg (x - y)) (div_nonneg (Real.sqrt_nonneg 3) hN.le)).mp hSq
  -- G5/G6: exact integer interval length, monotone cube, and fixed natural ceiling.
  · have hCardQ : Q.card = (Finset.Icc a b).card ^ 3 :=
      Fintype.card_piFinset_const (Finset.Icc a b) 3
    have hCardI : I.card ≤ Q.card := Finset.card_filter_le _ _
    have hCardInt : ((Finset.Icc a b).card : ℤ) = b + 1 - a :=
      Int.card_Icc_of_le a b (by omega)
    have hCardReal : ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by
      exact_mod_cast hCardInt
    have hFloorHi : (b : ℝ) ≤ B * (n : ℝ) := Int.floor_le _
    have hFloorLo : -B * (n : ℝ) < (a : ℝ) + 1 := Int.lt_floor_add_one _
    have hLength : ((Finset.Icc a b).card : ℝ) ≤ (2 * B + 4) * (n : ℝ) := by
      rw [hCardReal]
      nlinarith only [hFloorHi, hFloorLo, hNOne]
    have hCube : (((Finset.Icc a b).card : ℝ)) ^ 3 ≤
        ((2 * B + 4) * (n : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hLength 3
    have hCeil : (2 * B + 4) ^ 3 ≤ (Nat.ceil ((2 * B + 4) ^ 3) : ℝ) := Nat.le_ceil _
    have hReal : (I.card : ℝ) ≤ ((Nat.ceil ((2 * B + 4) ^ 3) * n ^ 3 : ℕ) : ℝ) := by
      calc
        (I.card : ℝ) ≤ (Q.card : ℝ) := by exact_mod_cast hCardI
        _ = (((Finset.Icc a b).card : ℝ)) ^ 3 := by rw [hCardQ, Nat.cast_pow]
        _ ≤ ((2 * B + 4) * (n : ℝ)) ^ 3 := hCube
        _ = (2 * B + 4) ^ 3 * (n : ℝ) ^ 3 := mul_pow _ _ _
        _ ≤ (Nat.ceil ((2 * B + 4) ^ 3) : ℝ) * (n : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right hCeil (pow_nonneg hN.le _)
        _ = ((Nat.ceil ((2 * B + 4) ^ 3) * n ^ 3 : ℕ) : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_pow]
    exact (Nat.cast_le (α := ℝ)).mp hReal
  -- G8: actual center membership transfers the unchanged original 2d buffer.
  · intro D d _hd hRoom nu
    exact hRoom (center nu) (subset_closure (hCenter nu).1)

end OAI.AnisotropicCalderon.Regularity
