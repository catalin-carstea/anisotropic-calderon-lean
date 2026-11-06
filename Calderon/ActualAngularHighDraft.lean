import Calderon.ActualAngularRadialRemainderTopology
import Calderon.ActualAngularFirstOrderMaps
import Calderon.ActualAngularCoordinateJets

import Calderon.ActualRawAdjointDegreeGainedHighDraft
import Calderon.ActualReferenceAdjointHighRotationSecondRemainder
import Calderon.ActualAdjointSmoothMultiplierCanonicalJointGainTransferJointRegularity
import Calderon.ActualAdjointRadialSmoothMultiplierSignedTaylorFactor
import Calderon.NativeLinearCoordinateMultiplierIdentification
import Calderon.SphereSobolevCoordinateInclusion
import Calderon.ActualReferenceSharpRotationRemainderDensityGraph
import Calderon.ActualReferenceDegreeGainedHighSecondRemainder
import Calderon.ActualReferenceDegreeSecondRemainderRawGraph
import Calderon.ActualHighSmoothMultiplierSecondRadialRemainderCoercivity
import Calderon.LocalSmoothSignedTaylorRemainder
import Calderon.CompactInverseDerivativeBounds
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.WithLp


set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff ENNReal Topology InnerProductSpace

/-! ## Generic typed finite cancellations and within-jet caps (MATHEMATICS.md §3–§5) -/

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularHighDraft

section GenericV025

variable {E F N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- MATHEMATICS.md §1: generic lowering cancellation. -/
private lemma loweringCancelV025 (J : F →L[ℝ] N) (Th : E →L[ℝ] F) (Tl : F →L[ℝ] N)
    (Rh : Fin 3 → E →L[ℝ] F) (Rl : Fin 3 → F →L[ℝ] N) (Bh : E →L[ℝ] F) (Bl : F →L[ℝ] N)
    (Ml : Fin 3 → F →L[ℝ] F) (Mn : Fin 3 → N →L[ℝ] N) (Cr : Fin 3 → E →L[ℝ] F)
    (Cd : E →L[ℝ] F) (G : Fin 3 → F →L[ℝ] F) (i : Fin 3)
    (h1 : ∀ j v, J (Ml j v) = Mn j (J v))
    (h2 : ∀ j v, J (Cr j v) = Rl j (Th v) - Tl (Rh j v))
    (h3 : ∀ v, J (Cd v) = Bl (Th v) - Tl (Bh v))
    (h4 : ∀ j v, J (G j v) = Tl (Ml j v) - Mn j (Tl v)) (u : E) :
    J (((∑ j : Fin 3, ((Ml j).comp (Cr j) - (G j).comp (Rh j))) + (Ml i).comp Cd -
        (G i).comp Bh) u) =
      ((∑ j : Fin 3, (Mn j).comp (Rl j)) + (Mn i).comp Bl) (Th u) -
        Tl (((∑ j : Fin 3, (Ml j).comp (Rh j)) + (Ml i).comp Bh) u) := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, map_add, map_sub, map_sum,
    h1, h2, h3, h4]
  simp only [Finset.sum_sub_distrib]
  abel

/-- MATHEMATICS.md §2: generic raising cancellation. -/
private lemma raisingCancelV025 (I : E →L[ℝ] F) (J : F →L[ℝ] N) (Sh : E →L[ℝ] F)
    (Sl : F →L[ℝ] N) (Rh : Fin 3 → E →L[ℝ] F) (Rl : Fin 3 → F →L[ℝ] N) (Bh : E →L[ℝ] F)
    (Bl : F →L[ℝ] N) (Mh : Fin 3 → E →L[ℝ] E) (Ml : Fin 3 → F →L[ℝ] F)
    (Cr : Fin 3 → E →L[ℝ] F) (Cd : E →L[ℝ] F) (Gh : Fin 3 → E →L[ℝ] E) (i : Fin 3)
    (k1 : ∀ j x, J (Rh j x) = Rl j (I x)) (k1' : ∀ x, J (Bh x) = Bl (I x))
    (k2 : ∀ j x, I (Gh j x) = Sh (Mh j x) - Ml j (Sh x))
    (k3 : ∀ j x, J (Cr j x) = Rl j (Sh x) - Sl (Rh j x))
    (k3' : ∀ x, J (Cd x) = Bl (Sh x) - Sl (Bh x)) (u : E) :
    J (((∑ j : Fin 3, ((Rh j).comp (Gh j) - (Cr j).comp (Mh j))) - Bh.comp (Gh i) +
        Cd.comp (Mh i)) u) =
      ((-∑ j : Fin 3, (Rl j).comp (Ml j)) + Bl.comp (Ml i)) (Sh u) -
        Sl (((-∑ j : Fin 3, (Rh j).comp (Mh j)) + Bh.comp (Mh i)) u) := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    map_add, map_sub, map_neg, map_sum, k1, k1', k2, k3, k3']
  simp only [Finset.sum_sub_distrib, map_sub]
  abel

/-- MATHEMATICS.md §4: generic within-jet caps on a compact set. -/
private lemma compactJetCapV025 {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (f : P → W) (s : Set P) (hs : IsCompact s)
    (hU : UniqueDiffOn ℝ s) (hf : ContDiffOn ℝ ∞ f s) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ p ∈ s, ‖iteratedFDerivWithin ℝ n f s p‖ ≤ M := by
  have hC : ∀ n : ℕ, ∃ C : ℝ, ∀ p ∈ s, ‖iteratedFDerivWithin ℝ n f s p‖ ≤ C := fun n =>
    hs.exists_bound_of_continuousOn
      (hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hU)
  induction N with
  | zero =>
    obtain ⟨C, hC0⟩ := hC 0
    refine ⟨max C 0, le_max_right _ _, fun n hn p hp => ?_⟩
    have hn0 : n = 0 := Nat.le_zero.mp hn
    subst hn0
    exact (hC0 p hp).trans (le_max_left _ _)
  | succ N ih =>
    obtain ⟨M, hM0, hM⟩ := ih
    obtain ⟨C, hCN⟩ := hC (N + 1)
    refine ⟨max M C, hM0.trans (le_max_left _ _), fun n hn p hp => ?_⟩
    rcases Nat.lt_or_ge n (N + 1) with h | h
    · exact (hM n (Nat.lt_succ_iff.mp h) p hp).trans (le_max_left _ _)
    · have hnN : n = N + 1 := le_antisymm hn h
      subst hnN
      exact (hCN p hp).trans (le_max_right _ _)

/-- MATHEMATICS.md §5: generic common-room assembly. All destructuring happens on free
variables of this abstract goal. -/
private theorem roomAssemblyV025 {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Room : ℝ → Set P) (Ω : Set P) (ρ : ℝ) (Seg : P → Prop)
    (Up Low : Fin 3 → P → V → Prop) (Gr : (Fin 3 → P → V) → Fin 3 → P → Prop)
    (Ca : (Fin 3 → P → V) → Fin 3 → P → W)
    (hmono : ∀ δ δ' : ℝ, δ ≤ δ' → Room δ ⊆ Room δ')
    (hcpt : ∀ δ, IsCompact (Room δ)) (hUD : ∀ δ, 0 < δ → UniqueDiffOn ℝ (Room δ))
    (hSegOf : ∀ δ, Room δ ⊆ Ω → ∀ p ∈ Room δ, Seg p)
    (hΩ : ∃ δ, 0 < δ ∧ δ ≤ ρ ∧ Room δ ⊆ Ω)
    (hFam : ∃ d, 0 < d ∧ d ≤ ρ ∧ ∃ G : Fin 3 → P → V,
      (∀ j, ContDiffOn ℝ ∞ (G j) (Room d)) ∧
      ∀ j, ∀ p ∈ Room d, Up j p (G j p) ∧ (Seg p → Low j p (G j p)))
    (hGr : ∀ G i p, Seg p → (∀ j, Low j p (G j p)) → Gr G i p)
    (hCa : ∀ G δ, 0 < δ → Room δ ⊆ Ω → (∀ j, ContDiffOn ℝ ∞ (G j) (Room δ)) →
      ∀ i, ContDiffOn ℝ ∞ (Ca G i) (Room δ)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ Room δ ⊆ Ω ∧ ∃ G : Fin 3 → P → V,
      (∀ j, ContDiffOn ℝ ∞ (G j) (Room δ)) ∧
      (∀ j, ∀ p ∈ Room δ, Up j p (G j p) ∧ Low j p (G j p)) ∧
      ∀ i, (∀ p ∈ Room δ, Gr G i p) ∧ ContDiffOn ℝ ∞ (Ca G i) (Room δ) ∧
        ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ p ∈ Room δ,
          ‖iteratedFDerivWithin ℝ n (Ca G i) (Room δ) p‖ ≤ M := by
  obtain ⟨δΩ, hδΩ, _hδΩρ, hRoomΩ⟩ := hΩ
  obtain ⟨d, hd, hdρ, G, hGs, hGp⟩ := hFam
  have hδ : 0 < min δΩ d := lt_min hδΩ hd
  have hsub : Room (min δΩ d) ⊆ Room d := hmono _ _ (min_le_right _ _)
  have hRoom : Room (min δΩ d) ⊆ Ω := (hmono _ _ (min_le_left _ _)).trans hRoomΩ
  have hS := hSegOf _ hRoom
  have hGOn : ∀ j, ContDiffOn ℝ ∞ (G j) (Room (min δΩ d)) := fun j => (hGs j).mono hsub
  have hUL : ∀ j, ∀ p ∈ Room (min δΩ d), Up j p (G j p) ∧ Low j p (G j p) :=
    fun j p hp => ⟨(hGp j p (hsub hp)).1, (hGp j p (hsub hp)).2 (hS p hp)⟩
  have hCaOn := hCa G _ hδ hRoom hGOn
  exact ⟨min δΩ d, hδ, (min_le_right _ _).trans hdρ, hRoom, G, hGOn, hUL, fun i =>
    ⟨fun p hp => hGr G i p (hS p hp) (fun j => (hUL j p hp).2), hCaOn i,
      fun N => compactJetCapV025 (Ca G i) (Room (min δΩ d)) (hcpt _) (hUD _ hδ) (hCaOn i) N⟩⟩

end GenericV025

/-! ## Actual setting -/

open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "NegH" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)

attribute [local instance] angularHighHalfCompleteSpace angularHighNegativeCompleteSpace

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

local notation "Mh" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ)
  (EuclideanSpace.single j (1 : ℝ))
local notation "Ml" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ)
  (EuclideanSpace.single j (1 : ℝ))
local notation "Mn" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ))
  (EuclideanSpace.single j (1 : ℝ))

/-! ### §3 Actual lowering commutator `[a,T]` -/

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hreg : FixedDirichletRegularity) (hg : IsAdmissibleMetric g)
  (hKernel : UnitBallValueTraceKernel τ0)

local notation "Ω" => referenceRadialEndpointInvertibleLocus
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0

/-- The full closed common room `[0,1] × closedBall y0 ρ × [-δ,δ]`. -/
def commonRoom (δ : ℝ) : Set Pphys := Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ)

lemma commonRoom_mono {δ δ' : ℝ} (h : δ ≤ δ') : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ' :=
  fun p hp => ⟨hp.1, hp.2.1, ⟨by linarith [hp.2.2.1], by linarith [hp.2.2.2]⟩⟩

lemma isCompact_commonRoom (δ : ℝ) : IsCompact (commonRoom y0 ρ δ) :=
  isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)

lemma uniqueDiffOn_commonRoom {δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    UniqueDiffOn ℝ (commonRoom y0 ρ δ) := by
  apply uniqueDiffOn_convex
  · exact (convex_Icc (0 : ℝ) 1).prod ((convex_closedBall y0 ρ).prod (convex_Icc _ _))
  · refine ⟨((1/2 : ℝ),(y0,(0 : ℝ))),
      interior_maximal (t := Ioo (0 : ℝ) 1 ×ˢ (ball y0 ρ ×ˢ Ioo (-δ) δ)) ?_ ?_
        ⟨⟨?_,?_⟩,mem_ball_self hρ,⟨?_,?_⟩⟩⟩
    · exact prod_mono Ioo_subset_Icc_self (prod_mono ball_subset_closedBall Ioo_subset_Icc_self)
    · exact isOpen_Ioo.prod (isOpen_ball.prod isOpen_Ioo)
    · norm_num
    · norm_num
    · linarith
    · exact hδ

lemma segment_of_mem_commonRoom {δ : ℝ} (hRoom : commonRoom y0 ρ δ ⊆ Ω)
    (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) :
    ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω := by
  intro θ hθ
  have ht : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
  have hr : |p.2.2| ≤ δ := abs_le.mpr hp.2.2
  have htr : |θ*p.2.2| ≤ δ := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans (by simpa only [one_mul] using hr)
  exact hRoom ⟨hp.1,hp.2.1,abs_le.mp htr⟩

/-- Completed ALL-Hi adjoint rotation gain `CrT_{ji}`. -/
def adjointRotationGain (j i : Fin 3) (p : Pphys) : Hi →L[ℝ] Half :=
  secondTaylorRemainder (fun z : ℝ => referenceAdjointHighAngleDerivativeFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i (p.1,(p.2.1,z))) p.2.2

/-- v011 adjoint degree gain `CdT`. -/
def adjointDegreeGain (p : Pphys) : Hi →L[ℝ] Half :=
  RawAdjointDegreeGainDraft.gainedHighSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p.1 p.2.1 p.2.2

/-- Formula (11): `CaT_i = Σ_j (Ml_j CrT_{ji} - G_j Rh_{ji}) + Ml_i CdT - G_i Bh`. -/
def loweringAngularHighCommutator (G : Fin 3 → Pphys → Half →L[ℝ] Half) (i : Fin 3)
    (p : Pphys) : Hi →L[ℝ] Half :=
  (∑ j : Fin 3, ((Ml j).comp
      (adjointRotationGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData j i p) -
    (G j p).comp (sphereSobolevRotationL (3/2 : ℝ) j i))) +
  (Ml i).comp (adjointDegreeGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg p) -
  (G i p).comp (sphereSobolevShiftedDegreeL (3/2 : ℝ))

local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "CaT" => loweringAngularHighCommutator hcalc hF hO hD τ0
  g L y0 Φ B ε C ρ H a w hData hreg

/-- Theorem A at one point, given the lower graph (h4) of the multiplier gains at that
point. The final theorem below discharges (h4) from actual producers. -/
lemma loweringAngularHighCommutator_graph (G : Fin 3 → Pphys → Half →L[ℝ] Half)
    (i : Fin 3) (p : Pphys) (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω)
    (hG : ∀ j v, sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (G j p v) =
      Tl p ((Ml j) v) - (Mn j) (Tl p v)) (u : Hi) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (CaT G i p u) =
      loweringLow hF hO hD i (Th p u) - Tl p (loweringHigh hF hO hD i u) := by
  have h1 (j : Fin 3) (v : Half) :
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) ((Ml j) v) =
        (Mn j) (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v) :=
    sphereSobolevInclusionL_linearCoordinateMul hF hO hD (1/2 : ℝ) (-(1/2 : ℝ))
      (by norm_num) (EuclideanSpace.single j (1 : ℝ)) v
  have h2 (j : Fin 3) (v : Hi) :
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (adjointRotationGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData j i p v) =
      sphereSobolevRotationL (1/2 : ℝ) j i (Th p v) -
        Tl p (sphereSobolevRotationL (3/2 : ℝ) j i v) :=
    (referenceAdjointHighAngleSecondRemainder_completed_rotation_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg j i p.1 p.2.1 p.2.2 hSeg v).symm
  have h3 (v : Hi) :
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
        (adjointDegreeGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg p v) =
      sphereSobolevShiftedDegreeL (1/2 : ℝ) (Th p v) -
        Tl p (sphereSobolevShiftedDegreeL (3/2 : ℝ) v) :=
    RawAdjointDegreeGainDraft.gainedHighSecondRemainder_signed_adjoint_degree_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p.1 p.2.1 p.2.2 hSeg v
  unfold loweringAngularHighCommutator loweringLow loweringHigh
  exact loweringCancelV025
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) (Th p) (Tl p)
    (fun j => sphereSobolevRotationL (3/2 : ℝ) j i) (fun j => sphereSobolevRotationL (1/2 : ℝ) j i)
    (sphereSobolevShiftedDegreeL (3/2 : ℝ)) (sphereSobolevShiftedDegreeL (1/2 : ℝ))
    (fun j => Ml j) (fun j => Mn j)
    (fun j => adjointRotationGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData j i p)
    (adjointDegreeGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg p)
    (fun j => G j p) i h1 h2 h3 hG u

include hreg in
lemma contDiffAt_adjointRotationGain (j i : Fin 3) (p : Pphys)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω) :
    ContDiffAt ℝ ∞ (adjointRotationGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData j i) p := by
  let F : (ℝ × R3) × ℝ → Hi →L[ℝ] Half := fun z =>
    referenceAdjointHighAngleDerivativeFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i (z.1.1,(z.1.2,z.2))
  let Ωs : Set ((ℝ × R3) × ℝ) := {z | (z.1.1,(z.1.2,z.2)) ∈ Ω}
  have hOpen := isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hΩs : IsOpen Ωs :=
    hOpen.preimage (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hFSmooth : ContDiffOn ℝ ∞ F Ωs := by
    intro z hz
    have hi : (z.1.1,(z.1.2,z.2)) ∈ Ω := hz
    exact (((contDiffOn_referenceAdjointHighAngleDerivativeFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i hreg).contDiffAt
        (hOpen.mem_nhds hi)).comp
      (f := fun v : (ℝ × R3) × ℝ => (v.1.1,(v.1.2,v.2))) z
        (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))).contDiffWithinAt
  have hR : ContDiffAt ℝ ∞
      (fun z : (ℝ × R3) × ℝ => secondTaylorRemainder (fun t : ℝ => F (z.1,t)) z.2)
        ((p.1,p.2.1),p.2.2) :=
    contDiffAt_secondTaylorRemainder_joint_of_open_segment F Ωs hΩs hFSmooth (p.1,p.2.1) p.2.2 hSeg
  have hOut := hR.comp (f := fun z : Pphys => ((z.1,z.2.1),z.2.2)) p
    ((contDiffAt_fst.prodMk contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)
  -- the goal has `adjointRotationGain … j i` unapplied: replace it by an explicit equality
  have hEq : adjointRotationGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData j i =
      (fun z : (ℝ × R3) × ℝ => secondTaylorRemainder (fun t : ℝ => F (z.1,t)) z.2) ∘
        (fun z : Pphys => ((z.1,z.2.1),z.2.2)) := by
    funext x
    rfl
  rw [hEq]
  exact hOut

/-! ### §4 Final actual theorem: one common room, exact graphs, smoothness, caps -/

/- Gains facade (MATHEMATICS.md §5): the canonical coordinate Half→Half gains on one room,
with the upper graph everywhere and the lower graph (h4) under the segment condition. -/
include hreg hKernel in
private lemma exists_coordinateGains_v025 :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ ∃ G : Fin 3 → Pphys → Half →L[ℝ] Half,
      (∀ j : Fin 3, ContDiffOn ℝ ∞ (G j) (commonRoom y0 ρ d)) ∧
      ∀ j : Fin 3, ∀ p ∈ commonRoom y0 ρ d,
        (∀ u : Hi, G j p (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u) =
          sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
            (secondTaylorRemainder (fun tau : ℝ =>
              referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
                g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (coordinateJets j)
                  (p.1,(p.2.1,tau))) p.2.2 u)) ∧
        ((∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω) →
          ∀ v : Half, sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (G j p v) =
            Tl p ((Ml j) v) - (Mn j) (Tl p v)) := by
  have hJets := exists_reference_commonRadius_adjointSmoothMultiplier_canonical_joint_jets
      (T := ℝ) g L y0 Φ B ε C ρ H a w hData hg hcalc hreg hF hO hD τ0
  obtain ⟨d,hd,hdρ,_hd1,hFamily⟩ := hJets
  have hj : ∀ j : Fin 3, ∃ G : (Pphys × ℝ) → Half →L[ℝ] Half,
      ContDiffOn ℝ ∞ G (commonRoom y0 ρ d ×ˢ (univ : Set ℝ)) ∧
      ∀ z ∈ commonRoom y0 ρ d ×ˢ (univ : Set ℝ),
        (∀ u : Hi, G z (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u) =
          sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
            (secondTaylorRemainder (fun tau : ℝ =>
              referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
                g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
                  (commonSupportCoefficientFamily 3 (coordinateCoefficient j)
                    (contDiff_coordinateCoefficient j) (closedBall (0 : R3) 2)
                    (isCompact_closedBall _ _) (coordinateCoefficient_support j) z.2)
                  (z.1.1,(z.1.2.1,tau))) z.1.2.2 u)) ∧
        (∀ v : Half, sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (G z v) =
          (-realHalfOperatorAdjointL (secondTaylorRemainder (fun tau : ℝ =>
            referenceSmoothMultiplierBoundaryCommutatorFamily
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
                (commonSupportCoefficientFamily 3 (coordinateCoefficient j)
                  (contDiff_coordinateCoefficient j) (closedBall (0 : R3) 2)
                  (isCompact_closedBall _ _) (coordinateCoefficient_support j) z.2)
                (z.1.1,(z.1.2.1,tau))) z.1.2.2))
            (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v)) := by
    intro j
    have hFj := hFamily (coordinateCoefficient j)
      (contDiff_coordinateCoefficient j) (closedBall (0 : R3) 2) (isCompact_closedBall _ _)
      (coordinateCoefficient_support j)
    obtain ⟨G,hGs,hGg,_hGc⟩ := hFj
    exact ⟨G,hGs,fun z hz => ⟨(hGg z hz).1,(hGg z hz).2.1⟩⟩
  choose G0 hG0s hG0g using hj
  have hMaps : MapsTo (fun p : Pphys => (p,(0 : ℝ))) (commonRoom y0 ρ d)
      (commonRoom y0 ρ d ×ˢ (univ : Set ℝ)) :=
    fun p hp => ⟨hp, mem_univ _⟩
  refine ⟨d,hd,hdρ,fun j p => G0 j (p,(0 : ℝ)),
    fun j => (hG0s j).comp (contDiff_id.prodMk contDiff_const).contDiffOn hMaps, ?_⟩
  intro j p hp
  refine ⟨fun u => (hG0g j (p,(0 : ℝ)) (hMaps hp)).1 u, fun hSeg v => ?_⟩
  have hlow := (hG0g j (p,(0 : ℝ)) (hMaps hp)).2 v
  have hfac := (referenceAdjointHalfRadialSecondRemainder_smoothMultiplier_negative_factor
    g L y0 Φ B ε C ρ H a w hData (coordinateCoefficient j) (contDiff_coordinateCoefficient j)
    (closedBall (0 : R3) 2) (isCompact_closedBall _ _) (coordinateCoefficient_support j)
    hcalc hF hO hD τ0 hKernel p.1 p.2.1 p.2.2 (0 : ℝ) hSeg).1 v
  calc
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (G0 j (p,(0 : ℝ)) v) =
        -(realHalfOperatorAdjointL (secondTaylorRemainder (fun tau : ℝ =>
          referenceSmoothMultiplierBoundaryCommutatorFamily
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (coordinateJets j)
              (p.1,(p.2.1,tau))) p.2.2)
          (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v)) := by
      rw [← ContinuousLinearMap.neg_apply]
      exact hlow
    _ = Tl p (nativeHalfCoefficientMulL hcalc hF hO hD τ0
            (smoothMultiplierLowerJets (coordinateJets j)) v) -
          nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
            (smoothMultiplierLowerJets (coordinateJets j)) (Tl p v) := hfac.symm
    _ = Tl p ((Ml j) v) - (Mn j) (Tl p v) :=
      congrArg₂ (fun (A : Half →L[ℝ] Half) (A' : NegH →L[ℝ] NegH) => Tl p (A v) - A' (Tl p v))
        (coordinateJets_half hcalc hF hO hD τ0 j) (coordinateJets_negativeHalf hcalc hF hO hD τ0 j)

/-- Smoothness facade: smooth coordinate gains on a room inside Ω give a smooth `CaT`. -/
private lemma contDiffOn_loweringAngularHigh_v025 (G : Fin 3 → Pphys → Half →L[ℝ] Half)
    (δ : ℝ) (hRoom : commonRoom y0 ρ δ ⊆ Ω)
    (hGOn : ∀ j : Fin 3, ContDiffOn ℝ ∞ (G j) (commonRoom y0 ρ δ)) (i : Fin 3) :
    ContDiffOn ℝ ∞ (CaT G i) (commonRoom y0 ρ δ) := by
  have hSeg (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) :=
    segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom p hp
  have hCrOn (j : Fin 3) : ContDiffOn ℝ ∞
      (adjointRotationGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData j i)
      (commonRoom y0 ρ δ) := fun p hp =>
    (contDiffAt_adjointRotationGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
      j i p (hSeg p hp)).contDiffWithinAt
  have hCdOn : ContDiffOn ℝ ∞
      (adjointDegreeGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg)
      (commonRoom y0 ρ δ) := fun p hp =>
    (RawAdjointDegreeGainDraft.contDiffAt_gainedHighSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p.1 p.2.1 p.2.2
        (hSeg p hp)).contDiffWithinAt
  have hEq : CaT G i = fun p =>
      (∑ j : Fin 3, ((Ml j).comp
          (adjointRotationGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData j i p) -
        (G j p).comp (sphereSobolevRotationL (3/2 : ℝ) j i))) +
      (Ml i).comp (adjointDegreeGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg p) -
      (G i p).comp (sphereSobolevShiftedDegreeL (3/2 : ℝ)) := rfl
  rw [hEq]
  apply ContDiffOn.sub
  · apply ContDiffOn.add
    · apply ContDiffOn.sum
      intro j _
      exact (contDiffOn_const.clm_comp (hCrOn j)).sub ((hGOn j).clm_comp contDiffOn_const)
    · exact contDiffOn_const.clm_comp hCdOn
  · exact (hGOn i).clm_comp contDiffOn_const

include hreg hg hKernel in
theorem exists_reference_commonRadius_loweringAngularHigh_graph_caps :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
    ∃ G : Fin 3 → Pphys → Half →L[ℝ] Half,
      (∀ j : Fin 3, ContDiffOn ℝ ∞ (G j) (commonRoom y0 ρ δ)) ∧
      (∀ j : Fin 3, ∀ p ∈ commonRoom y0 ρ δ,
        (∀ u : Hi, G j p (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u) =
          sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
            (secondTaylorRemainder (fun tau : ℝ =>
              referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
                g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (coordinateJets j)
                  (p.1,(p.2.1,tau))) p.2.2 u)) ∧
        (∀ v : Half, sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (G j p v) =
          Tl p ((Ml j) v) - (Mn j) (Tl p v))) ∧
      ∀ i : Fin 3,
        (∀ p ∈ commonRoom y0 ρ δ, ∀ u : Hi,
          sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (CaT G i p u) =
            loweringLow hF hO hD i (Th p u) - Tl p (loweringHigh hF hO hD i u)) ∧
        ContDiffOn ℝ ∞ (CaT G i) (commonRoom y0 ρ δ) ∧
        ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ p ∈ commonRoom y0 ρ δ,
          ‖iteratedFDerivWithin ℝ n (CaT G i) (commonRoom y0 ρ δ) p‖ ≤ M := by
  have hρ : 0 < ρ := hData.1.2.1
  have hΩ := exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  have hFam := exists_coordinateGains_v025 hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
    hreg hg hKernel
  exact roomAssemblyV025 (commonRoom y0 ρ) Ω ρ
    (fun p : Pphys => ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω)
    (fun (j : Fin 3) (p : Pphys) (A : Half →L[ℝ] Half) =>
      ∀ u : Hi, A (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u) =
        sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
          (secondTaylorRemainder (fun tau : ℝ =>
            referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
              g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (coordinateJets j)
                (p.1,(p.2.1,tau))) p.2.2 u))
    (fun (j : Fin 3) (p : Pphys) (A : Half →L[ℝ] Half) =>
      ∀ v : Half, sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (A v) =
        Tl p ((Ml j) v) - (Mn j) (Tl p v))
    (fun (G : Fin 3 → Pphys → Half →L[ℝ] Half) (i : Fin 3) (p : Pphys) =>
      ∀ u : Hi, sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (CaT G i p u) =
        loweringLow hF hO hD i (Th p u) - Tl p (loweringHigh hF hO hD i u))
    (fun (G : Fin 3 → Pphys → Half →L[ℝ] Half) (i : Fin 3) => CaT G i)
    (fun _ _ h => commonRoom_mono y0 ρ h)
    (fun δ => isCompact_commonRoom y0 ρ δ)
    (fun _ hδ => uniqueDiffOn_commonRoom y0 ρ hρ hδ)
    (fun _ hRoom p hp =>
      segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom p hp)
    hΩ hFam
    (fun G i p hSeg hLow u =>
      loweringAngularHighCommutator_graph hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
        hreg G i p hSeg (fun j v => hLow j v) u)
    (fun G δ _ hRoom hGOn i =>
      contDiffOn_loweringAngularHigh_v025 hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
        G δ hRoom hGOn i)

/-
  -- the canonical Half→Half gains for the fixed coordinate coefficients
  have hj : ∀ j : Fin 3, ∃ G : (Pphys × ℝ) → Half →L[ℝ] Half,
      ContDiffOn ℝ ∞ G (commonRoom y0 ρ d ×ˢ (univ : Set ℝ)) ∧
      ∀ z ∈ commonRoom y0 ρ d ×ˢ (univ : Set ℝ),
        (∀ u : Hi, G z (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u) =
          sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
            (secondTaylorRemainder (fun tau : ℝ =>
              referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
                g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
                  (commonSupportCoefficientFamily 3 (coordinateCoefficient j)
                    (contDiff_coordinateCoefficient j) (closedBall (0 : R3) 2)
                    (isCompact_closedBall _ _) (coordinateCoefficient_support j) z.2)
                  (z.1.1,(z.1.2.1,tau))) z.1.2.2 u)) ∧
        (∀ v : Half, sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (G z v) =
          (-realHalfOperatorAdjointL (secondTaylorRemainder (fun tau : ℝ =>
            referenceSmoothMultiplierBoundaryCommutatorFamily
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
                (commonSupportCoefficientFamily 3 (coordinateCoefficient j)
                  (contDiff_coordinateCoefficient j) (closedBall (0 : R3) 2)
                  (isCompact_closedBall _ _) (coordinateCoefficient_support j) z.2)
                (z.1.1,(z.1.2.1,tau))) z.1.2.2))
            (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v)) := by
    intro j
    obtain ⟨G,hGs,hGg,_hGc⟩ := hFamily (coordinateCoefficient j)
      (contDiff_coordinateCoefficient j) (closedBall (0 : R3) 2) (isCompact_closedBall _ _)
      (coordinateCoefficient_support j)
    exact ⟨G,hGs,fun z hz => ⟨(hGg z hz).1,(hGg z hz).2.1⟩⟩
  choose G0 hG0s hG0g using hj
  let δ : ℝ := min δΩ d
  have hδ : 0 < δ := lt_min hδΩ hd
  have hδΩle : δ ≤ δΩ := min_le_left _ _
  have hδd : δ ≤ d := min_le_right _ _
  have hRoom : commonRoom y0 ρ δ ⊆ Ω :=
    (commonRoom_mono y0 ρ hδΩle).trans hRoomΩ
  have hSeg (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) :=
    segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom p hp
  have hMaps : MapsTo (fun p : Pphys => (p,(0 : ℝ))) (commonRoom y0 ρ δ)
      (commonRoom y0 ρ d ×ˢ (univ : Set ℝ)) :=
    fun p hp => ⟨commonRoom_mono y0 ρ hδd hp, mem_univ _⟩
  let G : Fin 3 → Pphys → Half →L[ℝ] Half := fun j p => G0 j (p,(0 : ℝ))
  have hGOn (j : Fin 3) : ContDiffOn ℝ ∞ (G j) (commonRoom y0 ρ δ) :=
    (hG0s j).comp (contDiff_id.prodMk contDiff_const).contDiffOn hMaps
  -- lower graph (h4) of the coordinate gains, from actual producers only
  have hGlow (j : Fin 3) (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) (v : Half) :
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (G j p v) =
        Tl p ((Ml j) v) - (Mn j) (Tl p v) := by
    have hlow := (hG0g j (p,(0 : ℝ)) (hMaps hp)).2 v
    have hfac := (referenceAdjointHalfRadialSecondRemainder_smoothMultiplier_negative_factor
      g L y0 Φ B ε C ρ H a w hData (coordinateCoefficient j) (contDiff_coordinateCoefficient j)
      (closedBall (0 : R3) 2) (isCompact_closedBall _ _) (coordinateCoefficient_support j)
      hcalc hF hO hD τ0 hKernel p.1 p.2.1 p.2.2 (0 : ℝ) (hSeg p hp)).1 v
    calc
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (G j p v) =
          -(realHalfOperatorAdjointL (secondTaylorRemainder (fun tau : ℝ =>
            referenceSmoothMultiplierBoundaryCommutatorFamily
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (coordinateJets j)
                (p.1,(p.2.1,tau))) p.2.2)
            (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v)) := by
        simpa only [ContinuousLinearMap.neg_apply] using hlow
      _ = Tl p (nativeHalfCoefficientMulL hcalc hF hO hD τ0
              (smoothMultiplierLowerJets (coordinateJets j)) v) -
            nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
              (smoothMultiplierLowerJets (coordinateJets j)) (Tl p v) := hfac.symm
      _ = Tl p ((Ml j) v) - (Mn j) (Tl p v) := by
        rw [coordinateJets_half hcalc hF hO hD τ0 j,
          coordinateJets_negativeHalf hcalc hF hO hD τ0 j]
  -- joint smoothness of the gains on the room
  have hCrOn (j i : Fin 3) : ContDiffOn ℝ ∞
      (adjointRotationGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData j i)
      (commonRoom y0 ρ δ) := fun p hp =>
    (contDiffAt_adjointRotationGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
      j i p (hSeg p hp)).contDiffWithinAt
  have hCdOn : ContDiffOn ℝ ∞
      (adjointDegreeGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg)
      (commonRoom y0 ρ δ) := fun p hp =>
    (RawAdjointDegreeGainDraft.contDiffAt_gainedHighSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p.1 p.2.1 p.2.2
        (hSeg p hp)).contDiffWithinAt
  have hCaTOn (i : Fin 3) : ContDiffOn ℝ ∞ (CaT G i) (commonRoom y0 ρ δ) := by
    have hEq : CaT G i = fun p =>
        (∑ j : Fin 3, ((Ml j).comp
            (adjointRotationGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData j i p) -
          (G j p).comp (sphereSobolevRotationL (3/2 : ℝ) j i))) +
        (Ml i).comp (adjointDegreeGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg p) -
        (G i p).comp (sphereSobolevShiftedDegreeL (3/2 : ℝ)) := rfl
    rw [hEq]
    apply ContDiffOn.sub
    · apply ContDiffOn.add
      · apply ContDiffOn.sum
        intro j _
        exact (contDiffOn_const.clm_comp (hCrOn j i)).sub ((hGOn j).clm_comp contDiffOn_const)
      · exact contDiffOn_const.clm_comp hCdOn
    · exact (hGOn i).clm_comp contDiffOn_const
  refine ⟨δ,hδ,hδd.trans hdρ,hRoom,G,hGOn,?_,?_⟩
  · intro j p hp
    refine ⟨?_,hGlow j p hp⟩
    intro u
    exact (hG0g j (p,(0 : ℝ)) (hMaps hp)).1 u
  · intro i
    refine ⟨?_,hCaTOn i,?_⟩
    · intro p hp u
      exact loweringAngularHighCommutator_graph hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
        hreg G i p (hSeg p hp) (fun j v => hGlow j p hp v) u
    · intro N
      exact exists_compact_iteratedFDerivWithin_bound (CaT G i) (commonRoom y0 ρ δ)
        (isCompact_commonRoom y0 ρ δ) (uniqueDiffOn_commonRoom y0 ρ hρ hδ) (hCaTOn i) N
-/

/-! ### §5 Raising commutator `[A,S]`: actual definition and REDUCTION (not final)

The only hypothesis `hSharpMultiplier` is literally the graph of the unexposed owner
`ActualHighSmoothMultiplierSecondRadialRemainderGraph` for the fixed coordinate jets.
See MISSING-SOURCES.md. -/

/-- Formula (1): `CAS_i = Σ_j (Rh_{ji} Gh_j - CrS_{ji} Mh_j) - Bh Gh_i + CdS Mh_i`. -/
def raisingAngularHighCommutator (i : Fin 3) (q : ℝ) (y : R3) (r : ℝ) : Hi →L[ℝ] Half :=
  (∑ j : Fin 3, ((sphereSobolevRotationL (3/2 : ℝ) j i).comp
      (referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (coordinateJets j) q y r) -
    (referenceSharpRadialRotationSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i q y r).comp (Mh j))) -
  (sphereSobolevShiftedDegreeL (3/2 : ℝ)).comp
    (referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (coordinateJets i) q y r) +
  (referenceRadialDegreeCommutatorGainedHighSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q y r).comp (Mh i)

theorem raisingAngularHighCommutator_graph_of_sharpMultiplierGraph
    (i : Fin 3) (q : ℝ) (y : R3) (r : ℝ)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ Ω)
    (hSharpMultiplier : ∀ (j : Fin 3) (f : Hi),
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        (referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (coordinateJets j) q y r f) =
      referenceSharpRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (coordinateJets j) f) -
      nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets (coordinateJets j))
        (referenceSharpRadialTraceSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r f))
    (u : Hi) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (raisingAngularHighCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg i q y r u) =
    ((-∑ j : Fin 3, (sphereSobolevRotationL (1/2 : ℝ) j i).comp (Ml j)) +
        (sphereSobolevShiftedDegreeL (1/2 : ℝ)).comp (Ml i))
      (referenceSharpRadialTraceSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r u) -
    referenceLowerRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
      (((-∑ j : Fin 3, (sphereSobolevRotationL (3/2 : ℝ) j i).comp (Mh j)) +
        (sphereSobolevShiftedDegreeL (3/2 : ℝ)).comp (Mh i)) u) := by
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Sh := referenceSharpRadialTraceSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
  let Sl := referenceLowerRadialTraceSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
  have k1 (j : Fin 3) (x : Hi) :
      J (sphereSobolevRotationL (3/2 : ℝ) j i x) = sphereSobolevRotationL (1/2 : ℝ) j i (I x) :=
    congrArg (fun A : Hi →L[ℝ] NegH => A x) (sphereSobolevRotationL_threehalf_half_compatibility j i)
  have k1' (x : Hi) :
      J (sphereSobolevShiftedDegreeL (3/2 : ℝ) x) = sphereSobolevShiftedDegreeL (1/2 : ℝ) (I x) :=
    congrArg (fun A : Hi →L[ℝ] NegH => A x) sphereSobolevShiftedDegree_high_half_compatibility
  have k2 (j : Fin 3) (x : Hi) :
      I (referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (coordinateJets j) q y r x) =
        Sh ((Mh j) x) - (Ml j) (Sh x) := by
    -- explicit equality elimination instead of a `rw` motive over the physical statement
    exact (hSharpMultiplier j x).trans
      (congrArg₂ (fun (A : Hi →L[ℝ] Hi) (A' : Half →L[ℝ] Half) => Sh (A x) - A' (Sh x))
        (coordinateJets_threeHalf hcalc hF hO hD τ0 j) (coordinateJets_half hcalc hF hO hD τ0 j))
  have k3 (j : Fin 3) (x : Hi) :
      J (referenceSharpRadialRotationSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i q y r x) =
        sphereSobolevRotationL (1/2 : ℝ) j i (Sh x) - Sl (sphereSobolevRotationL (3/2 : ℝ) j i x) :=
    referenceSharpRadialRotationSecondRemainder_weak_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i q y r hSeg x
  have k3' (x : Hi) :
      J (referenceRadialDegreeCommutatorGainedHighSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q y r x) =
        sphereSobolevShiftedDegreeL (1/2 : ℝ) (Sh x) - Sl (sphereSobolevShiftedDegreeL (3/2 : ℝ) x) := by
    have hc := DFunLike.congr_fun
      (referenceRadialDegreeCommutatorGainedHighSecondRemainder_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q y r hSeg) x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at hc
    have hr := referenceRadialDegreeCommutatorHalfSecondRemainder_raw_degree_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q y r hSeg x
    exact hc.trans hr
  unfold raisingAngularHighCommutator
  exact raisingCancelV025 I J Sh Sl
    (fun j => sphereSobolevRotationL (3/2 : ℝ) j i) (fun j => sphereSobolevRotationL (1/2 : ℝ) j i)
    (sphereSobolevShiftedDegreeL (3/2 : ℝ)) (sphereSobolevShiftedDegreeL (1/2 : ℝ))
    (fun j => Mh j) (fun j => Ml j)
    (fun j => referenceSharpRadialRotationSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i q y r)
    (referenceRadialDegreeCommutatorGainedHighSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q y r)
    (fun j => referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (coordinateJets j) q y r)
    i k1 k1' k2 k3 k3' u


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularHighDraft
