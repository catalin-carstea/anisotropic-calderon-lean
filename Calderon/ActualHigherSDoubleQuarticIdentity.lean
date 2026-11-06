import Calderon.ActualFullEPhysicalEndpoints

/-! Author proof source for the exact Double/Double four-pairing identity.
This source is UNCOMPILED. It asserts no actual Calderon specialization,
analytic bound, final callback premise, or acceptance.
Before-source expansion and exact signature: ../upfront-v001/.
-/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSDoubleQuarticIdentity

variable {Hi Half Neg Phys ι : Type*}
  [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Half] [NormedSpace ℝ Half]
  [NormedAddCommGroup Neg] [NormedSpace ℝ Neg]
  [NormedAddCommGroup Phys] [InnerProductSpace ℝ Phys]

/-- A genuine low pivot and the two high graphs give both physical adjunctions.
No density argument or upward Sobolev inclusion is assumed. -/
lemma high_pairings_of_low_pivot
    (I : Hi →L[ℝ] Half) (J : Half →L[ℝ] Neg) (K : Half →L[ℝ] Phys)
    (PP : Half →L[ℝ] Neg →L[ℝ] ℝ)
    (A B : ι → Hi →L[ℝ] Half) (AL BL : ι → Half →L[ℝ] Neg)
    (hA : ∀ a x, J (A a x) = AL a (I x))
    (hB : ∀ a x, J (B a x) = BL a (I x))
    (hPivot : ∀ a x y, PP x (AL a y) = PP y (BL a x))
    (hPair : ∀ x z, PP x (J z) = ⟪K x, K z⟫_ℝ) :
    (∀ a x z, ⟪K (A a x), K z⟫_ℝ = PP (I x) (BL a z)) ∧
      (∀ a x z, ⟪K (B a x), K z⟫_ℝ = PP (I x) (AL a z)) := by
  constructor
  · intro a x z
    calc
      _ = ⟪K z, K (A a x)⟫_ℝ := real_inner_comm _ _
      _ = PP z (J (A a x)) := (hPair _ _).symm
      _ = PP z (AL a (I x)) := congrArg (PP z) (hA a x)
      _ = PP (I x) (BL a z) := hPivot a z (I x)
  · intro a x z
    calc
      _ = ⟪K z, K (B a x)⟫_ℝ := real_inner_comm _ _
      _ = PP z (J (B a x)) := (hPair _ _).symm
      _ = PP z (BL a (I x)) := congrArg (PP z) (hB a x)
      _ = PP (I x) (AL a z) := (hPivot a (I x) z).symm

/-- The entire ordered Double/Double quartic difference, with four plus signs. -/
lemma double_word_pairing_sub_reverse_eq_four_pairings
    (I : Hi →L[ℝ] Half) (J : Half →L[ℝ] Neg) (K : Half →L[ℝ] Phys)
    (PP : Half →L[ℝ] Neg →L[ℝ] ℝ)
    (A B : ι → Hi →L[ℝ] Half) (AL BL : ι → Half →L[ℝ] Neg)
    (G : ι → ι → Hi →L[ℝ] Half) (Cl : ι → ι → Half →L[ℝ] Neg)
    (hJ : Function.Injective J)
    (hA : ∀ a x, J (A a x) = AL a (I x))
    (hB : ∀ a x, J (B a x) = BL a (I x))
    (hG : ∀ a b x, J (G a b x) = BL a (A b x) - AL b (B a x))
    (hCl : ∀ a b x, Cl a b (I x) = J (G a b x))
    (hAdjA : ∀ a x z, ⟪K (A a x), K z⟫_ℝ = PP (I x) (BL a z))
    (hAdjB : ∀ a x z, ⟪K (B a x), K z⟫_ℝ = PP (I x) (AL a z))
    (hPair : ∀ x z, PP x (J z) = ⟪K x, K z⟫_ℝ)
    (U : Hi) (V v : ι → Hi)
    (hV : ∀ a, I (V a) = A a U) (hv : ∀ a, I (v a) = B a U)
    (i j k l : ι) :
    ⟪K (A i (V j)), K (A k (V l))⟫_ℝ -
      ⟪K (B j (v i)), K (B l (v k))⟫_ℝ =
      PP (A j U) (Cl i k (A l U)) +
      PP (A j U) (AL k (G i l U)) +
      PP (G k j U) (AL l (B i U)) +
      PP (B k U) (Cl j l (B i U)) := by
  have hExchange (a b : ι) (x y : Hi) :
      ⟪K (A a x), K (A b y)⟫_ℝ =
        PP (I x) (Cl a b (I y)) + ⟪K (B b x), K (B a y)⟫_ℝ := by
    have hrow : BL a (A b y) = J (G a b y) + AL b (B a y) := by
      rw [hG a b y]
      abel
    calc
      _ = PP (I x) (BL a (A b y)) := hAdjA a x (A b y)
      _ = PP (I x) (J (G a b y)) + PP (I x) (AL b (B a y)) := by
        rw [hrow, map_add]
      _ = PP (I x) (Cl a b (I y)) + ⟪K (B b x), K (B a y)⟫_ℝ := by
        rw [hCl a b y, hAdjB b x (B a y)]
  have hBiVl : B i (V l) = A l (v i) + G i l U := by
    apply hJ
    rw [map_add, hB i (V l), hA l (v i), hV l, hv i, hG i l U]
    abel
  have hBkVj : B k (V j) = A j (v k) + G k j U := by
    apply hJ
    rw [map_add, hB k (V j), hA j (v k), hV j, hv k, hG k j U]
    abel
  have hthird : ⟪K (G k j U), K (A l (v i))⟫_ℝ =
      PP (G k j U) (AL l (B i U)) := by
    calc
      _ = PP (G k j U) (J (A l (v i))) := (hPair _ _).symm
      _ = PP (G k j U) (AL l (B i U)) := by rw [hA l (v i), hv i]
  have hR : ⟪K (B k (V j)), K (B i (V l))⟫_ℝ =
      ⟪K (B k (V j)), K (A l (v i))⟫_ℝ +
        PP (A j U) (AL k (G i l U)) := by
    calc
      _ = ⟪K (B k (V j)), K (A l (v i))⟫_ℝ +
          ⟪K (B k (V j)), K (G i l U)⟫_ℝ := by
        rw [hBiVl, map_add, inner_add_right]
      _ = ⟪K (B k (V j)), K (A l (v i))⟫_ℝ +
          PP (A j U) (AL k (G i l U)) := by
        rw [hAdjB k (V j) (G i l U), hV j]
  have hR1 : ⟪K (B k (V j)), K (A l (v i))⟫_ℝ =
      ⟪K (A j (v k)), K (A l (v i))⟫_ℝ +
        PP (G k j U) (AL l (B i U)) := by
    rw [hBkVj, map_add, inner_add_left, hthird]
  have hlast : ⟪K (A j (v k)), K (A l (v i))⟫_ℝ =
      PP (B k U) (Cl j l (B i U)) +
        ⟪K (B l (v k)), K (B j (v i))⟫_ℝ := by
    simpa only [hv] using hExchange j l (v k) (v i)
  have hfirst : ⟪K (A i (V j)), K (A k (V l))⟫_ℝ =
      PP (A j U) (Cl i k (A l U)) +
        ⟪K (B k (V j)), K (B i (V l))⟫_ℝ := by
    simpa only [hV] using hExchange i k (V j) (V l)
  rw [hR, hR1, hlast] at hfirst
  have hsym : ⟪K (B l (v k)), K (B j (v i))⟫_ℝ =
      ⟪K (B j (v i)), K (B l (v k))⟫_ℝ := real_inner_comm _ _
  linarith only [hfirst, hsym]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSDoubleQuarticIdentity
