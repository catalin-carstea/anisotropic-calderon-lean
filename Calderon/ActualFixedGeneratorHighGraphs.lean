import Calderon.ActualCanonicalGeneratorAngularGainedRows
import Calderon.ActualGeneratorEPairedGainedEndpoints
import Calderon.ActualFiniteHarmonicModelRotationLieCommutator
import Calderon.SphereSobolevSingleRotationAngleDerivative
import Calderon.SphereSobolevShiftedPhysicalDegree

/-! Fixed rotation/physical-degree paired gains. The full Sobolev Lie graph is proved here
from the harmonic singles and density. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFixedGeneratorPairedGains
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualCanonicalAngularGainedBracket ActualFiniteHarmonicModel
  ActualRetainedGeneratorMultiplierGains ActualGeneratorEPairedGainedEndpoints
  HarmonicDerivativeOperator RotationCasimir SmoothSphereRotationProjection
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "I33" => sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "RH" => sphereSobolevRotationL (3/2 : ℝ)
local notation "RL" => sphereSobolevRotationL (1/2 : ℝ)
local notation "DH" => sphereSobolevShiftedDegreeL (3/2 : ℝ)
local notation "DL" => sphereSobolevShiftedDegreeL (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

def rotationLieHigh (i j a b : Fin 3) : Hi →L[ℝ] Half :=
  (if j=a then RH i b else 0) - (if j=b then RH i a else 0) -
    (if i=a then RH j b else 0) + (if i=b then RH j a else 0)

/-- The first rotation is reversed, so the rotation/rotation Lie combination is NEGATED. -/
def fixedGeneratorGainHigh : Generator → Generator → Hi →L[ℝ] Half
  | Sum.inl ij, Sum.inl ab => -rotationLieHigh ij.1 ij.2 ab.1 ab.2
  | _, _ => 0


attribute [local irreducible] sphereSobolevRotationL sphereSobolevShiftedDegreeL
  sphereSobolevInclusionL sphereSobolevSingleL generatorHigh generatorLow
  generatorSharpHigh generatorSharpLow rotationLieHigh fixedGeneratorGainHigh

private lemma rotationHigh_single (i j : Fin 3) (k : ℕ) (U : harmonicSphereSubspace k) :
    RH i j (sphereSobolevSingleL (3/2 : ℝ) k U) =
      sphereSobolevSingleL (1/2 : ℝ) k (harmonicSphereRotation k i j U) := by
  simpa only [sphereSobolevSingleL, show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num] using
    sphereSobolevRotationL_single (3/2 : ℝ) i j k U

private lemma rotationLow_single (i j : Fin 3) (k : ℕ) (U : harmonicSphereSubspace k) :
    RL i j (sphereSobolevSingleL (1/2 : ℝ) k U) =
      sphereSobolevSingleL (-(1/2 : ℝ)) k (harmonicSphereRotation k i j U) := by
  simpa only [sphereSobolevSingleL, show (1/2 : ℝ)-1 = (-(1/2) : ℝ) by norm_num] using
    sphereSobolevRotationL_single (1/2 : ℝ) i j k U

private lemma degreeHigh_single (k : ℕ) (U : harmonicSphereSubspace k) :
    DH (sphereSobolevSingleL (3/2 : ℝ) k U) =
      (k : ℝ) • sphereSobolevSingleL (1/2 : ℝ) k U := by
  simpa only [sphereSobolevSingleL, show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num] using
    sphereSobolevShiftedDegreeL_single (3/2 : ℝ) k U

private lemma degreeLow_single (k : ℕ) (U : harmonicSphereSubspace k) :
    DL (sphereSobolevSingleL (1/2 : ℝ) k U) =
      (k : ℝ) • sphereSobolevSingleL (-(1/2 : ℝ)) k U := by
  simpa only [sphereSobolevSingleL, show (1/2 : ℝ)-1 = (-(1/2) : ℝ) by norm_num] using
    sphereSobolevShiftedDegreeL_single (1/2 : ℝ) k U

private lemma map_conditional_zero {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (P : Prop) [Decidable P] (u : E) :
    A (if P then u else 0) = if P then A u else 0 := by
  split_ifs <;> simp only [map_zero]

theorem rotationLieHigh_graph (i j a b : Fin 3) :
    (JL).comp (rotationLieHigh i j a b) =
      (RL i j).comp (RH a b) - (RL a b).comp (RH i j) := by
  apply sphereSobolev_clm_eq_of_single (3/2 : ℝ)
  intro k U
  have hSingle := congrArg (sphereSobolevSingleL (-(1/2 : ℝ)) k)
    (harmonicSphereRotation_lie_commutator k i j a b U)
  have hLift (s t : Fin 3) (P : Prop) [Decidable P] :
      JL ((if P then RH s t else 0) (sphereSobolevSingleL (3/2 : ℝ) k U)) =
        (if P then sphereSobolevSingleL (-(1/2 : ℝ)) k (harmonicSphereRotation k s t U) else 0) := by
    split_ifs <;> simp only [ContinuousLinearMap.zero_apply, map_zero,
      rotationHigh_single, sphereSobolevInclusionL_single]
  change JL (rotationLieHigh i j a b (sphereSobolevSingleL (3/2 : ℝ) k U)) =
    RL i j (RH a b (sphereSobolevSingleL (3/2 : ℝ) k U)) -
      RL a b (RH i j (sphereSobolevSingleL (3/2 : ℝ) k U))
  simp only [rotationLieHigh, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    map_add, map_sub, hLift, rotationHigh_single, rotationLow_single]
  have hNormalized :
      sphereSobolevSingleL (-(1/2 : ℝ)) k
          (harmonicSphereRotation k i j (harmonicSphereRotation k a b U)) -
        sphereSobolevSingleL (-(1/2 : ℝ)) k
          (harmonicSphereRotation k a b (harmonicSphereRotation k i j U)) =
      (if j=a then sphereSobolevSingleL (-(1/2 : ℝ)) k (harmonicSphereRotation k i b U) else 0) -
      (if j=b then sphereSobolevSingleL (-(1/2 : ℝ)) k (harmonicSphereRotation k i a U) else 0) -
      (if i=a then sphereSobolevSingleL (-(1/2 : ℝ)) k (harmonicSphereRotation k j b U) else 0) +
      (if i=b then sphereSobolevSingleL (-(1/2 : ℝ)) k (harmonicSphereRotation k j a U) else 0) := by
    simpa only [map_sub, map_add, map_conditional_zero] using hSingle
  exact hNormalized.symm

theorem degree_rotation_commute (i j : Fin 3) :
    (DL).comp (RH i j) = (RL i j).comp DH := by
  apply sphereSobolev_clm_eq_of_single (3/2 : ℝ)
  intro k U
  simp only [ContinuousLinearMap.comp_apply, rotationHigh_single, degreeLow_single,
    degreeHigh_single, rotationLow_single, map_smul]

theorem fixedGeneratorGainHigh_graph (V W : Generator) (U : Hi) :
    JL (fixedGeneratorGainHigh V W U) =
      generatorSharpLow V (generatorHigh W U) -
        generatorLow W (generatorSharpHigh V U) := by
  cases V with
  | inl ij =>
    cases W with
    | inl ab =>
      have hLie := congrArg (fun A : Hi →L[ℝ] Neg => A U)
        (rotationLieHigh_graph ij.1 ij.2 ab.1 ab.2)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply] at hLie
      simp only [fixedGeneratorGainHigh, generatorSharpLow, generatorSharpHigh,
        generatorHigh, generatorLow, ContinuousLinearMap.neg_apply, map_neg]
      rw [hLie]
      abel
    | inr z =>
      have hDeg := congrArg (fun A : Hi →L[ℝ] Neg => A U) (degree_rotation_commute ij.1 ij.2)
      simp only [ContinuousLinearMap.comp_apply] at hDeg
      simp only [fixedGeneratorGainHigh, generatorSharpLow, generatorSharpHigh,
        generatorHigh, generatorLow, ContinuousLinearMap.zero_apply, map_zero,
        ContinuousLinearMap.neg_apply, map_neg]
      exact (show -RL ij.1 ij.2 (DH U) - -DL (RH ij.1 ij.2 U) = 0 from
        (congrArg (fun z : Neg => -RL ij.1 ij.2 (DH U) - -z) hDeg).trans
          (sub_self (-RL ij.1 ij.2 (DH U)))).symm
  | inr z =>
    cases W with
    | inl ab =>
      have hDeg := congrArg (fun A : Hi →L[ℝ] Neg => A U) (degree_rotation_commute ab.1 ab.2)
      simp only [ContinuousLinearMap.comp_apply] at hDeg
      simp only [fixedGeneratorGainHigh, generatorSharpLow, generatorSharpHigh,
        generatorHigh, generatorLow, ContinuousLinearMap.zero_apply, map_zero]
      exact (sub_eq_zero.mpr hDeg).symm
    | inr z' =>
      simp only [fixedGeneratorGainHigh, generatorSharpLow, generatorSharpHigh,
        generatorHigh, generatorLow, ContinuousLinearMap.zero_apply, map_zero, sub_self]

private lemma generator_compat (V : Generator) (U : Hi) :
    JL (generatorHigh V U) = generatorLow V (IH U) := by
  cases V with
  | inl ij =>
    simpa only [generatorHigh, generatorLow, ContinuousLinearMap.comp_apply] using
      congrArg (fun A : Hi →L[ℝ] Neg => A U)
        (sphereSobolevRotationL_threehalf_half_compatibility ij.1 ij.2)
  | inr z =>
    simpa only [generatorHigh, generatorLow, ContinuousLinearMap.comp_apply] using
      congrArg (fun A : Hi →L[ℝ] Neg => A U) sphereSobolevShiftedDegree_high_half_compatibility

private lemma generatorSharp_compat (V : Generator) (U : Hi) :
    JL (generatorSharpHigh V U) = generatorSharpLow V (IH U) := by
  cases V with
  | inl ij =>
    simpa only [generatorSharpHigh, generatorSharpLow, ContinuousLinearMap.neg_apply, map_neg] using
      congrArg (fun z : Neg => -z) (generator_compat (Sum.inl ij) U)
  | inr z => simpa only [generatorSharpHigh, generatorSharpLow, generatorHigh, generatorLow] using
      generator_compat (Sum.inr z) U

private lemma generator_low_pivots (V : Generator) (x y : Half) :
    PP x (generatorLow V y) = PP y (generatorSharpLow V x) ∧
      PP x (generatorSharpLow V y) = PP y (generatorLow V x) := by
  cases V with
  | inl ij =>
    have h := sphereSobolevDualPairing_half_rotation_skew ij.1 ij.2 y x
    have hFirst : PP x (RL ij.1 ij.2 y) = -PP y (RL ij.1 ij.2 x) :=
      (real_inner_comm x (RL ij.1 ij.2 y)).symm.trans h
    constructor
    · simpa only [generatorLow, generatorSharpLow, ContinuousLinearMap.neg_apply,
        sphereSobolevDualPairing, inner_neg_right] using hFirst
    · have hSecond : -PP x (RL ij.1 ij.2 y) = PP y (RL ij.1 ij.2 x) := by
        linarith only [hFirst]
      simpa only [generatorLow, generatorSharpLow, ContinuousLinearMap.neg_apply,
        sphereSobolevDualPairing, inner_neg_right] using hSecond
  | inr z =>
    have h := sphereSobolevDualPairing_lower_distributionalTranspose DL y x
    rw [sphereLowerDistributionalTranspose_shiftedDegree_half] at h
    simpa only [generatorLow, generatorSharpLow] using And.intro h h

theorem fixedGeneratorGainHigh_paired (V W : Generator) (U Z : Hi) :
    PP (IH Z) (JL (fixedGeneratorGainHigh V W U)) =
      PP (IH U) (JL (fixedGeneratorGainHigh W V Z)) := by
  have hForward (A : Generator) (u : Hi) (x : Half) :
      PP (IH u) (generatorLow A x) = PP x (JL (generatorSharpHigh A u)) :=
    (generator_low_pivots A (IH u) x).1.trans
      (congrArg (PP x) (generatorSharp_compat A u).symm)
  have hReverse (A : Generator) (u : Hi) (x : Half) :
      PP (IH u) (generatorSharpLow A x) = PP x (JL (generatorHigh A u)) :=
    (generator_low_pivots A (IH u) x).2.trans
      (congrArg (PP x) (generator_compat A u).symm)
  have h1 : PP (IH Z) (generatorSharpLow V (generatorHigh W U)) =
      PP (IH U) (generatorSharpLow W (generatorHigh V Z)) :=
    (hReverse V Z (generatorHigh W U)).trans
      ((v016_pairing_inclusion_symm (generatorHigh W U) (generatorHigh V Z)).trans
        (hReverse W U (generatorHigh V Z)).symm)
  have h2 : PP (IH Z) (generatorLow W (generatorSharpHigh V U)) =
      PP (IH U) (generatorLow V (generatorSharpHigh W Z)) :=
    (hForward W Z (generatorSharpHigh V U)).trans
      ((v016_pairing_inclusion_symm (generatorSharpHigh V U) (generatorSharpHigh W Z)).trans
        (hForward V U (generatorSharpHigh W Z)).symm)
  have hleft := (congrArg (fun n : Neg => PP (IH Z) n)
    (fixedGeneratorGainHigh_graph V W U)).trans (v016_pairing_sub_right (IH Z) _ _)
  have hright := (congrArg (fun n : Neg => PP (IH U) n)
    (fixedGeneratorGainHigh_graph W V Z)).trans (v016_pairing_sub_right (IH U) _ _)
  exact hleft.trans ((congrArg₂ (fun x y : ℝ => x-y) h1 h2).trans hright.symm)


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFixedGeneratorPairedGains
