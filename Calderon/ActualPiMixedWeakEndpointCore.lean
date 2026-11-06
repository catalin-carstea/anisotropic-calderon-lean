import Calderon.SphereSobolevBalancedDualKernelRestriction
import Calderon.SphereSobolevBalancedDualInterpolationLinear
import Calderon.SphereSobolevBalancedDualEndpointExtension
import Calderon.SphereSobolevDualRiesz
import Calderon.SphereSobolevPhysicalCrossInclusionPairing
import Calderon.SphereSobolevPairingInclusion
import Calderon.NativeSmoothMultiplierCommonSupportJets

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter Metric
open scoped ContDiff ENNReal Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft
open SphereHarmonic

lemma v015_exists_iteratedFDerivWithin_cap {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (s : Set E)
    (hs : IsCompact s) (hu : UniqueDiffOn ℝ s) (hf : ContDiffOn ℝ ∞ f s) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ z ∈ s, ‖iteratedFDerivWithin ℝ n f s z‖ ≤ M := by
  have hB : ∀ n : ℕ, ∃ Cn : ℝ, ∀ z ∈ s, ‖iteratedFDerivWithin ℝ n f s z‖ ≤ Cn := fun n =>
    hs.exists_bound_of_continuousOn
      (hf.continuousOn_iteratedFDerivWithin (m := n) (by exact_mod_cast le_top) hu)
  choose Cn hCn using hB
  refine ⟨∑ n ∈ Finset.range (N+1), max (Cn n) 0,
    Finset.sum_nonneg (fun n _ => le_max_right _ _), ?_⟩
  intro n hn z hz
  calc ‖iteratedFDerivWithin ℝ n f s z‖ ≤ Cn n := hCn n z hz
    _ ≤ max (Cn n) 0 := le_max_left _ _
    _ ≤ ∑ n ∈ Finset.range (N+1), max (Cn n) 0 :=
      Finset.single_le_sum (f := fun n => max (Cn n) 0) (fun n _ => le_max_right _ _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "NegH" => SphereSobolev (-(1/2 : ℝ))
local notation "Neg3" => SphereSobolev (-(3/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "I13" => sphereSobolevInclusionL (1/2 : ℝ) (-(3/2 : ℝ)) (by norm_num)
local notation "I31" => sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "I33" => sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)

/-! ### §0 Pairing algebra (the pairing is the real inner product, as in its definition) -/

lemma v016_pairing_sub_right (x : Half) (v v' : NegH) : PP x (v - v') = PP x v - PP x v' := by
  show ⟪x, v - v'⟫_ℝ = ⟪x, v⟫_ℝ - ⟪x, v'⟫_ℝ
  exact inner_sub_right _ _ _

/-- (sym) `⟨x, JL y⟩_{1/2} = ⟨y, JL x⟩_{1/2}`: both equal the H⁰ inner product
(`sphereSobolevDualPairing_inclusion_eq_inner_zero`). -/
lemma v016_pairing_inclusion_symm (x y : Half) : PP x (JL y) = PP y (JL x) := by
  have hx := sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2 : ℝ) (by norm_num) y x
  have hy := sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2 : ℝ) (by norm_num) x y
  have h1 : PP x (JL y) = sphereSobolevDualPairing (-(1/2 : ℝ)) (JL y) x := real_inner_comm _ _
  have h2 : PP y (JL x) = sphereSobolevDualPairing (-(1/2 : ℝ)) (JL x) y := real_inner_comm _ _
  rw [h1, h2, hx, hy]
  exact real_inner_comm _ _

/-! ### §1 The Riesz transpose of a high map -/

/-- `innerSL` on `Half`, read as the pairing `Half × Neg → ℝ`. The carriers coincide, exactly as in
the definition `sphereSobolevDualPairing s u v := ⟪u, v⟫_ℝ`. -/
def v016HalfPairingL : Half →L[ℝ] NegH →L[ℝ] ℝ := innerSL ℝ

lemma v016HalfPairingL_apply (x : Half) (v : NegH) : v016HalfPairingL x v = PP x v := rfl

/-- `D ↦ Dᵗ`, `⟨u, Dᵗ v⟩_{3/2} = ⟨D u, v⟩_{1/2}`; continuous linear in `D`. -/
def v016TransposeL : (Hi →L[ℝ] Half) →L[ℝ] (NegH →L[ℝ] Neg3) :=
  (ContinuousLinearMap.compL ℝ NegH (StrongDual ℝ Hi) Neg3
      (sphereSobolevDualRieszL (3/2 : ℝ))).comp
    (((ContinuousLinearMap.compL ℝ NegH (Half →L[ℝ] ℝ) (Hi →L[ℝ] ℝ)).flip
        v016HalfPairingL.flip).comp
      (ContinuousLinearMap.compL ℝ Hi Half ℝ).flip)

lemma v016TransposeL_apply (D : Hi →L[ℝ] Half) (v : NegH) :
    v016TransposeL D v = sphereSobolevDualRieszL (3/2 : ℝ) ((v016HalfPairingL.flip v).comp D) :=
  rfl

lemma v016TransposeL_pairing (D : Hi →L[ℝ] Half) (v : NegH) (u : Hi) :
    sphereSobolevDualPairing (3/2 : ℝ) u (v016TransposeL D v) = PP (D u) v := by
  rw [v016TransposeL_apply]
  exact sphereSobolevDualPairing_dualRiesz (3/2 : ℝ) ((v016HalfPairingL.flip v).comp D) u

lemma norm_v016TransposeL_apply_le (D : Hi →L[ℝ] Half) : ‖v016TransposeL D‖ ≤ ‖D‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D) (fun v => ?_)
  rw [v016TransposeL_apply, norm_sphereSobolevDualRieszL_apply]
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg D) (norm_nonneg v)) (fun u => ?_)
  have h1 : |PP (D u) v| ≤ ‖D u‖ * ‖v‖ := abs_sphereSobolevDualPairing_le (1/2 : ℝ) (D u) v
  have h2 : ‖D u‖ ≤ ‖D‖ * ‖u‖ := D.le_opNorm u
  have h3 : ‖((v016HalfPairingL.flip v).comp D) u‖ = |PP (D u) v| := Real.norm_eq_abs _
  rw [h3]
  calc |PP (D u) v| ≤ ‖D u‖ * ‖v‖ := h1
    _ ≤ (‖D‖ * ‖u‖) * ‖v‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg v)
    _ = ‖D‖ * ‖v‖ * ‖u‖ := by ring

/-! ### §2 Lemma A: paired adjunction ⇒ balanced endpoint compatibility -/

lemma v016_compatible_of_adjunction (Ch Dh : Hi →L[ℝ] Half)
    (hAdj : ∀ u w : Hi, PP (IH w) (JL (Ch u)) = PP (IH u) (JL (Dh w))) :
    (I13).comp Ch = (v016TransposeL Dh).comp I31 := by
  refine ContinuousLinearMap.ext (fun u => ?_)
  -- `SphereSobolev s` is the common `lp` carrier and `⟨w, x⟩_{3/2}` is `⟪w, x⟫_ℝ`, so it suffices
  -- to compare all `⟨w, ·⟩_{3/2}`, `w : Hi` (`ext_inner_left`).
  have key : ∀ w : Hi, sphereSobolevDualPairing (3/2 : ℝ) w (I13 (Ch u)) =
      sphereSobolevDualPairing (3/2 : ℝ) w (v016TransposeL Dh (I31 u)) := fun w =>
    calc sphereSobolevDualPairing (3/2 : ℝ) w (I13 (Ch u))
        = sphereSobolevDualPairing (-(1/2 : ℝ)) (I31 w) (Ch u) :=
          sphereSobolevDualPairing_threeHalf_cross_inclusion w (Ch u)
      _ = sphereSobolevDualPairing (-(1/2 : ℝ)) (JL (Ch u)) (IH w) :=
          sphereSobolevDualPairing_half_cross_inclusion_comm w (Ch u)
      _ = PP (IH w) (JL (Ch u)) := real_inner_comm _ _
      _ = PP (IH u) (JL (Dh w)) := hAdj u w
      _ = sphereSobolevDualPairing (-(1/2 : ℝ)) (JL (Dh w)) (IH u) := real_inner_comm _ _
      _ = sphereSobolevDualPairing (-(1/2 : ℝ)) (I31 u) (Dh w) :=
          (sphereSobolevDualPairing_half_cross_inclusion_comm u (Dh w)).symm
      _ = PP (Dh w) (I31 u) := real_inner_comm _ _
      _ = sphereSobolevDualPairing (3/2 : ℝ) w (v016TransposeL Dh (I31 u)) :=
          (v016TransposeL_pairing Dh (I31 u) w).symm
  simp only [ContinuousLinearMap.comp_apply]
  exact ext_inner_left ℝ key

lemma v016_adjunction_swap (Ch Dh : Hi →L[ℝ] Half)
    (hAdj : ∀ u w : Hi, PP (IH w) (JL (Ch u)) = PP (IH u) (JL (Dh w))) :
    ∀ u w : Hi, PP (IH w) (JL (Dh u)) = PP (IH u) (JL (Ch w)) :=
  fun u w => (hAdj w u).symm

/-! ### §3 Generic smooth low-endpoint family on a closed UniqueDiffOn set -/

/-- The conclusions of `v016_exists_contDiffOn_lowEndpoint` for any `C^∞` family `R` of compatible
endpoints whose underlying pair is `(Dh zᵗ, Ch z)` on `S` (canonical interpolation of `R`). -/
lemma v019_lowEndpoint_of_restriction {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X) (Ch Dh : X → Hi →L[ℝ] Half)
    (R : X → sphereSobolevBalancedDualCompatibleEndpoints) (hR : ContDiffOn ℝ ∞ R S)
    (hv : ∀ z ∈ S, (R z).1 =
      ((v016TransposeL (Dh z), Ch z) : SphereSobolevBalancedDualEndpointPair)) :
    ∃ Cl : X → Half →L[ℝ] NegH, ContDiffOn ℝ ∞ Cl S ∧ ∀ z ∈ S,
      (Cl z).comp IH = (JL).comp (Ch z) ∧
      (I33).comp (Cl z) = (v016TransposeL (Dh z)).comp JL ∧
      ‖Cl z‖ ≤ (‖v016TransposeL (Dh z)‖ + ‖Ch z‖) / 2 ∧
      ‖Cl z‖ ≤ (‖Dh z‖ + ‖Ch z‖) / 2 := by
  refine ⟨fun z => sphereSobolevBalancedDualInterpolationL (R z),
    contDiff_sphereSobolevBalancedDualInterpolationL.comp_contDiffOn hR, fun z hz => ?_⟩
  have h1 : (R z).1.1 = v016TransposeL (Dh z) := congrArg Prod.fst (hv z hz)
  have h2 : (R z).1.2 = Ch z := congrArg Prod.snd (hv z hz)
  have hUp : (sphereSobolevBalancedDualInterpolationL (R z)).comp IH = (JL).comp (Ch z) :=
    (sphereSobolevBalancedDualInterpolationL_upper_inclusion (R z)).trans
      (congrArg (fun A : Hi →L[ℝ] Half => (JL).comp A) h2)
  have hLo : (I33).comp (sphereSobolevBalancedDualInterpolationL (R z)) =
      (v016TransposeL (Dh z)).comp JL :=
    (sphereSobolevBalancedDualInterpolationL_lower_inclusion (R z)).trans
      (congrArg (fun A : NegH →L[ℝ] Neg3 => A.comp JL) h1)
  have hN0 : ‖sphereSobolevBalancedDualInterpolationL (R z)‖ ≤
      (‖(R z).1.1‖ + ‖(R z).1.2‖) / 2 :=
    (congrArg (fun A : Half →L[ℝ] NegH => ‖A‖)
      (sphereSobolevBalancedDualInterpolationL_apply (R z))).le.trans
      (norm_sphereSobolevBalancedDualEndpointL_le (R z).1.1 (R z).1.2
        ((sphereSobolevBalancedDualCompatible_mem_iff (R z).1).mp (R z).2))
  have hN1 : ‖sphereSobolevBalancedDualInterpolationL (R z)‖ ≤
      (‖v016TransposeL (Dh z)‖ + ‖Ch z‖) / 2 :=
    hN0.trans_eq (congrArg₂ (fun (A : NegH →L[ℝ] Neg3) (B : Hi →L[ℝ] Half) =>
      (‖A‖ + ‖B‖) / 2) h1 h2)
  have hT : ‖v016TransposeL (Dh z)‖ ≤ ‖Dh z‖ := norm_v016TransposeL_apply_le (Dh z)
  have hN2 : ‖sphereSobolevBalancedDualInterpolationL (R z)‖ ≤ (‖Dh z‖ + ‖Ch z‖) / 2 := by
    linarith
  exact ⟨hUp, hLo, hN1, hN2⟩

theorem v016_exists_contDiffOn_lowEndpoint {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : Set X) (hU : UniqueDiffOn ℝ S) (Ch Dh : X → Hi →L[ℝ] Half)
    (hC : ContDiffOn ℝ ∞ Ch S) (hD : ContDiffOn ℝ ∞ Dh S)
    (hAdj : ∀ z ∈ S, ∀ u w : Hi, PP (IH w) (JL (Ch z u)) = PP (IH u) (JL (Dh z w))) :
    ∃ Cl : X → Half →L[ℝ] NegH, ContDiffOn ℝ ∞ Cl S ∧ ∀ z ∈ S,
      (Cl z).comp IH = (JL).comp (Ch z) ∧
      (I33).comp (Cl z) = (v016TransposeL (Dh z)).comp JL ∧
      ‖Cl z‖ ≤ (‖v016TransposeL (Dh z)‖ + ‖Ch z‖) / 2 ∧
      ‖Cl z‖ ≤ (‖Dh z‖ + ‖Ch z‖) / 2 := by
  have hE : ∀ z ∈ S, ((v016TransposeL (Dh z), Ch z) : SphereSobolevBalancedDualEndpointPair) ∈
      sphereSobolevBalancedDualCompatibleEndpoints := fun z hz =>
    (sphereSobolevBalancedDualCompatible_mem_iff (v016TransposeL (Dh z), Ch z)).mpr
      (v016_compatible_of_adjunction (Ch z) (Dh z) (hAdj z hz))
  have hSmooth : ContDiffOn ℝ ∞
      (fun z => ((v016TransposeL (Dh z), Ch z) : SphereSobolevBalancedDualEndpointPair)) S :=
    ((ContinuousLinearMap.contDiff v016TransposeL).comp_contDiffOn hD).prodMk hC
  exact v019_lowEndpoint_of_restriction S Ch Dh
    (sphereSobolevBalancedDualCompatibleRestriction
      (fun z => ((v016TransposeL (Dh z), Ch z) : SphereSobolevBalancedDualEndpointPair)) S hE)
    (contDiffOn_sphereSobolevBalancedDualCompatibleRestriction S hU
      (fun z => ((v016TransposeL (Dh z), Ch z) : SphereSobolevBalancedDualEndpointPair))
      hSmooth hE)
    (fun z hz => sphereSobolevBalancedDualCompatibleRestriction_val
      (fun z => ((v016TransposeL (Dh z), Ch z) : SphereSobolevBalancedDualEndpointPair))
      S hE z hz)

/-! ### §4 One cap per `N` for all `i k` and two lower maps -/

lemma v016_exists_uniform_cap_two {X F₁ F₂ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    (S : Set X) (hS : IsCompact S) (hU : UniqueDiffOn ℝ S)
    (f₁ : Fin 3 → Fin 3 → X → F₁) (f₂ : Fin 3 → Fin 3 → X → F₂)
    (h₁ : ∀ i k, ContDiffOn ℝ ∞ (f₁ i k) S) (h₂ : ∀ i k, ContDiffOn ℝ ∞ (f₂ i k) S) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i k : Fin 3, ∀ n : ℕ, n ≤ N → ∀ z ∈ S,
      ‖iteratedFDerivWithin ℝ n (f₁ i k) S z‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (f₂ i k) S z‖ ≤ M := by
  choose M1 hM1 using fun i k : Fin 3 =>
    v015_exists_iteratedFDerivWithin_cap (f₁ i k) S hS hU (h₁ i k) N
  choose M2 hM2 using fun i k : Fin 3 =>
    v015_exists_iteratedFDerivWithin_cap (f₂ i k) S hS hU (h₂ i k) N
  have h0 (i k : Fin 3) : 0 ≤ M1 i k + M2 i k := add_nonneg (hM1 i k).1 (hM2 i k).1
  have hle (i k : Fin 3) :
      M1 i k + M2 i k ≤ ∑ i' : Fin 3, ∑ k' : Fin 3, (M1 i' k' + M2 i' k') :=
    (Finset.single_le_sum (f := fun k' => M1 i k' + M2 i k') (fun k' _ => h0 i k')
        (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun i' => ∑ k' : Fin 3, (M1 i' k' + M2 i' k'))
        (fun i' _ => Finset.sum_nonneg (fun k' _ => h0 i' k')) (Finset.mem_univ i))
  refine ⟨∑ i' : Fin 3, ∑ k' : Fin 3, (M1 i' k' + M2 i' k'),
    Finset.sum_nonneg (fun i' _ => Finset.sum_nonneg (fun k' _ => h0 i' k')), ?_⟩
  intro i k n hn z hz
  have a1 := (hM1 i k).2 n hn z hz
  have a2 := (hM2 i k).2 n hn z hz
  have b1 := (hM1 i k).1
  have b2 := (hM2 i k).1
  have hl := hle i k
  exact ⟨by linarith, by linarith⟩

/-! ### §5a Generic algebraic mixed adjunction `[a,TΠ]^† = [ΠS,A]` (MATHEMATICS.md §5).
A general lemma about arbitrary operators. It is NOT a premise of any actual theorem. -/

theorem v016_mixed_adjunction_of_primitives
    (aL AL Tl Sl : Half →L[ℝ] NegH) (aH AH Th Sh Ch Dh : Hi →L[ℝ] Half)
    (PiH : Hi →L[ℝ] Hi) (PiL : Half →L[ℝ] Half) (PiN : NegH →L[ℝ] NegH)
    (hC : ∀ u, JL (Ch u) = aL (Th (PiH u)) - Tl (PiL (aH u)))
    (hD : ∀ w, JL (Dh w) = PiN (Sl (AH w)) - AL (PiL (Sh w)))
    (haA1 : ∀ (x : Hi) (y : Half), PP (IH x) (aL y) = PP y (JL (AH x)))
    (haA2 : ∀ (x : Hi) (y : Half), PP (aH x) (JL y) = PP (IH x) (AL y))
    (hsym : ∀ x y : Half, PP x (JL y) = PP y (JL x))
    (hTc : ∀ z : Hi, JL (Th z) = Tl (IH z))
    (hSc : ∀ z : Hi, Sl (IH z) = JL (Sh z))
    (hTt : ∀ u v : Half, PP v (Sl u) = PP u (Tl v))
    (hPic : ∀ z : Hi, IH (PiH z) = PiL (IH z))
    (hPiN : ∀ y : Half, JL (PiL y) = PiN (JL y))
    (hPis : ∀ (x : Half) (y : NegH), PP (PiL x) y = PP x (PiN y)) (u w : Hi) :
    PP (IH w) (JL (Ch u)) = PP (IH u) (JL (Dh w)) := by
  have hT1 : PP (IH w) (aL (Th (PiH u))) = PP (IH u) (PiN (Sl (AH w))) :=
    calc PP (IH w) (aL (Th (PiH u)))
        = PP (Th (PiH u)) (JL (AH w)) := haA1 w (Th (PiH u))
      _ = PP (AH w) (JL (Th (PiH u))) := hsym (Th (PiH u)) (AH w)
      _ = PP (AH w) (Tl (IH (PiH u))) := congrArg (PP (AH w)) (hTc (PiH u))
      _ = PP (IH (PiH u)) (Sl (AH w)) := (hTt (AH w) (IH (PiH u))).symm
      _ = PP (PiL (IH u)) (Sl (AH w)) :=
          congrArg (fun x : Half => PP x (Sl (AH w))) (hPic u)
      _ = PP (IH u) (PiN (Sl (AH w))) := hPis (IH u) (Sl (AH w))
  have hT2 : PP (IH w) (Tl (PiL (aH u))) = PP (IH u) (AL (PiL (Sh w))) :=
    calc PP (IH w) (Tl (PiL (aH u)))
        = PP (PiL (aH u)) (Sl (IH w)) := (hTt (IH w) (PiL (aH u))).symm
      _ = PP (PiL (aH u)) (JL (Sh w)) := congrArg (PP (PiL (aH u))) (hSc w)
      _ = PP (aH u) (PiN (JL (Sh w))) := hPis (aH u) (JL (Sh w))
      _ = PP (aH u) (JL (PiL (Sh w))) := congrArg (PP (aH u)) (hPiN (Sh w)).symm
      _ = PP (IH u) (AL (PiL (Sh w))) := haA2 u (PiL (Sh w))
  calc PP (IH w) (JL (Ch u))
      = PP (IH w) (aL (Th (PiH u)) - Tl (PiL (aH u))) := congrArg (PP (IH w)) (hC u)
    _ = PP (IH w) (aL (Th (PiH u))) - PP (IH w) (Tl (PiL (aH u))) :=
        v016_pairing_sub_right (IH w) (aL (Th (PiH u))) (Tl (PiL (aH u)))
    _ = PP (IH u) (PiN (Sl (AH w))) - PP (IH u) (AL (PiL (Sh w))) :=
        congrArg₂ (fun a b : ℝ => a - b) hT1 hT2
    _ = PP (IH u) (PiN (Sl (AH w)) - AL (PiL (Sh w))) :=
        (v016_pairing_sub_right (IH u) (PiN (Sl (AH w))) (AL (PiL (Sh w)))).symm
    _ = PP (IH u) (JL (Dh w)) := congrArg (PP (IH u)) (hD w).symm


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft
end
