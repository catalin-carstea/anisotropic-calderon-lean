import Calderon.ActualCanonicalAngularGainedBracket
import Calderon.ActualFiniteHarmonicModelRotationShiftCommutator
import Calderon.SphereSobolevSingleRotationAngleDerivative
import Calderon.SphereSobolevShiftedPhysicalDegree
import Calderon.ActualAngularMixedEndpointPrimitives

/-! Source-only Sol author prerequisite for actual W/E. Upfront:
generator-angular-before-v001. Physical B has eigenvalue k, including zero.
This file is not the full W/E producer. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualCanonicalGeneratorAngularGainedRows
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft
  ActualCanonicalAngularGainedBracket ActualFiniteHarmonicModel
  HarmonicDerivativeOperator RotationCasimir ActualAngularPiDraft SmoothSphereRotationProjection
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
local notation "AH" => raisingHigh hF hO hD
local notation "AL" => raisingLow hF hO hD
local notation "aH" => loweringHigh hF hO hD
local notation "aL" => loweringLow hF hO hD
local notation "RH" => sphereSobolevRotationL (3/2 : ℝ)
local notation "RL" => sphereSobolevRotationL (1/2 : ℝ)
local notation "BH" => sphereSobolevShiftedDegreeL (3/2 : ℝ)
local notation "BL" => sphereSobolevShiftedDegreeL (1/2 : ℝ)

private lemma raisingHigh_single (a : Fin 3) (k : ℕ) (u : harmonicSphereSubspace k) :
    AH a (sphereSobolevSingleL (3/2 : ℝ) k u) =
      sphereSobolevSingleL (1/2 : ℝ) (k+1) (harmonicDerivativeAdjoint hF k a u) := by
  have h := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (3/2 : ℝ) a k u
  simpa only [raisingHigh,sphereSobolevAngularCoordinateTransposeL,sphereSobolevSingleL,
    ContinuousLinearMap.smul_apply,lp.singleContinuousLinearMap_apply,
    show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num] using h

private lemma raisingLow_single (a : Fin 3) (k : ℕ) (u : harmonicSphereSubspace k) :
    AL a (sphereSobolevSingleL (1/2 : ℝ) k u) =
      sphereSobolevSingleL (-(1/2 : ℝ)) (k+1) (harmonicDerivativeAdjoint hF k a u) := by
  have h := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (1/2 : ℝ) a k u
  simpa only [raisingLow,sphereSobolevAngularCoordinateTransposeL,sphereSobolevSingleL,
    ContinuousLinearMap.smul_apply,lp.singleContinuousLinearMap_apply,
    show (1/2 : ℝ)-1 = -(1/2 : ℝ) by norm_num] using h

private lemma rotationHigh_single (i j : Fin 3) (k : ℕ) (u : harmonicSphereSubspace k) :
    RH i j (sphereSobolevSingleL (3/2 : ℝ) k u) =
      sphereSobolevSingleL (1/2 : ℝ) k (harmonicSphereRotation k i j u) := by
  simpa only [sphereSobolevSingleL, show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num] using
    sphereSobolevRotationL_single (3/2 : ℝ) i j k u

private lemma rotationLow_single (i j : Fin 3) (k : ℕ) (u : harmonicSphereSubspace k) :
    RL i j (sphereSobolevSingleL (1/2 : ℝ) k u) =
      sphereSobolevSingleL (-(1/2 : ℝ)) k (harmonicSphereRotation k i j u) := by
  simpa only [sphereSobolevSingleL, show (1/2 : ℝ)-1 = (-(1/2) : ℝ) by norm_num] using
    sphereSobolevRotationL_single (1/2 : ℝ) i j k u

private lemma degreeHigh_single (k : ℕ) (u : harmonicSphereSubspace k) :
    BH (sphereSobolevSingleL (3/2 : ℝ) k u) =
      (k : ℝ) • sphereSobolevSingleL (1/2 : ℝ) k u := by
  simpa only [sphereSobolevSingleL, show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num] using
    sphereSobolevShiftedDegreeL_single (3/2 : ℝ) k u

private lemma degreeLow_single (k : ℕ) (u : harmonicSphereSubspace k) :
    BL (sphereSobolevSingleL (1/2 : ℝ) k u) =
      (k : ℝ) • sphereSobolevSingleL (-(1/2 : ℝ)) k u := by
  simpa only [sphereSobolevSingleL, show (1/2 : ℝ)-1 = (-(1/2) : ℝ) by norm_num] using
    sphereSobolevShiftedDegreeL_single (1/2 : ℝ) k u

/-- Literal canonical rotation/raising gain on the full high endpoint. -/
def rotationRaisingHigh (i j a : Fin 3) : Hi →L[ℝ] Half :=
  (if a=j then AH i else 0)-(if a=i then AH j else 0)
def rotationRaisingLow (i j a : Fin 3) : Half →L[ℝ] Neg :=
  (if a=j then AL i else 0)-(if a=i then AL j else 0)
def rotationLoweringHigh (i j a : Fin 3) : Hi →L[ℝ] Half :=
  (if a=j then aH i else 0)-(if a=i then aH j else 0)
def rotationLoweringLow (i j a : Fin 3) : Half →L[ℝ] Neg :=
  (if a=j then aL i else 0)-(if a=i then aL j else 0)

attribute [local irreducible] loweringHigh loweringLow raisingHigh raisingLow
  sphereSobolevRotationL sphereSobolevShiftedDegreeL sphereSobolevSingleL

/-- Exact full negative graph of [R_ij,A_a], extended from all harmonic singles. -/
theorem rotationRaisingHigh_graph (i j a : Fin 3) :
    (JL).comp (rotationRaisingHigh hF hO hD i j a) =
      (RL i j).comp (AH a)-(AL a).comp (RH i j) := by
  apply sphereSobolev_clm_eq_of_single (3/2 : ℝ)
  intro k u
  have hHarm := harmonicSphereRotation_raising_commutator hF k i j a u
  have hSingle := congrArg (sphereSobolevSingleL (-(1/2 : ℝ)) (k+1)) hHarm
  have hScalar :
      sphereSobolevSingleL (-(1/2 : ℝ)) (k+1)
        (harmonicSphereRotation (k+1) i j (harmonicDerivativeAdjoint hF k a u)) -
      sphereSobolevSingleL (-(1/2 : ℝ)) (k+1)
        (harmonicDerivativeAdjoint hF k a (harmonicSphereRotation k i j u)) =
      (if a=j then sphereSobolevSingleL (-(1/2 : ℝ)) (k+1) (harmonicDerivativeAdjoint hF k i u) else 0) -
      (if a=i then sphereSobolevSingleL (-(1/2 : ℝ)) (k+1) (harmonicDerivativeAdjoint hF k j u) else 0) := by
    simpa only [map_sub,apply_ite,map_zero] using hSingle
  have hLift (b : Fin 3) (P : Prop) [Decidable P] :
      JL ((if P then AH b else 0) (sphereSobolevSingleL (3/2 : ℝ) k u)) =
      (if P then sphereSobolevSingleL (-(1/2 : ℝ)) (k+1) (harmonicDerivativeAdjoint hF k b u) else 0) := by
    split_ifs <;> simp only [ContinuousLinearMap.zero_apply,map_zero,raisingHigh_single,sphereSobolevInclusionL_single]
  change JL (rotationRaisingHigh hF hO hD i j a (sphereSobolevSingleL (3/2 : ℝ) k u)) =
    RL i j (AH a (sphereSobolevSingleL (3/2 : ℝ) k u)) -
    AL a (RH i j (sphereSobolevSingleL (3/2 : ℝ) k u))
  simp only [rotationRaisingHigh,ContinuousLinearMap.sub_apply,map_sub,hLift,
    raisingHigh_single,raisingLow_single,rotationHigh_single,rotationLow_single]
  exact hScalar.symm

/-- Exact full negative graph of [R_ij,a_a], with the degree-zero branch retained. -/
theorem rotationLoweringHigh_graph (i j a : Fin 3) :
    (JL).comp (rotationLoweringHigh hF hO hD i j a) =
      (RL i j).comp (aH a)-(aL a).comp (RH i j) := by
  apply sphereSobolev_clm_eq_of_single (3/2 : ℝ)
  intro k u
  cases k with
  | zero =>
    have hzero : rotationLoweringHigh hF hO hD i j a (sphereSobolevSingleL (3/2 : ℝ) 0 u) = 0 := by
      simp only [rotationLoweringHigh,ContinuousLinearMap.sub_apply]
      split_ifs <;> simp only [loweringHigh_single_zero,ContinuousLinearMap.zero_apply,sub_self]
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,hzero,map_zero,rotationHigh_single,
      loweringHigh_single_zero,loweringLow_single_zero,sub_self]
  | succ k =>
    have hHarm := harmonicSphereRotation_derivative_commutator hF k i j a u
    have hSingle := congrArg (sphereSobolevSingleL (-(1/2 : ℝ)) k) hHarm
    have hScalar :
        sphereSobolevSingleL (-(1/2 : ℝ)) k
          (harmonicSphereRotation k i j (harmonicDerivative hF k a u)) -
        sphereSobolevSingleL (-(1/2 : ℝ)) k
          (harmonicDerivative hF k a (harmonicSphereRotation (k+1) i j u)) =
        (if a=j then sphereSobolevSingleL (-(1/2 : ℝ)) k (harmonicDerivative hF k i u) else 0) -
        (if a=i then sphereSobolevSingleL (-(1/2 : ℝ)) k (harmonicDerivative hF k j u) else 0) := by
      simpa only [map_sub,apply_ite,map_zero] using hSingle
    have hLift (b : Fin 3) (P : Prop) [Decidable P] :
        JL ((if P then aH b else 0) (sphereSobolevSingleL (3/2 : ℝ) (k+1) u)) =
        (if P then sphereSobolevSingleL (-(1/2 : ℝ)) k (harmonicDerivative hF k b u) else 0) := by
      split_ifs <;> simp only [ContinuousLinearMap.zero_apply,map_zero,loweringHigh_single_succ,sphereSobolevInclusionL_single]
    change JL (rotationLoweringHigh hF hO hD i j a (sphereSobolevSingleL (3/2 : ℝ) (k+1) u)) =
      RL i j (aH a (sphereSobolevSingleL (3/2 : ℝ) (k+1) u)) -
      aL a (RH i j (sphereSobolevSingleL (3/2 : ℝ) (k+1) u))
    simp only [rotationLoweringHigh,ContinuousLinearMap.sub_apply,map_sub,hLift,
      loweringHigh_single_succ,loweringLow_single_succ,rotationHigh_single,rotationLow_single]
    exact hScalar.symm

/-- The physical-degree raising gain is A, since its exact degree jump is +1. -/
theorem degreeRaisingHigh_graph (a : Fin 3) :
    (JL).comp (AH a) = (BL).comp (AH a)-(AL a).comp BH := by
  apply sphereSobolev_clm_eq_of_single (3/2 : ℝ)
  intro k u
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,raisingHigh_single,
    raisingLow_single,degreeHigh_single,degreeLow_single,map_smul,sphereSobolevInclusionL_single]
  have hScalar : (((k+1 : ℕ) : ℝ)-(k : ℝ))=1 := by push_cast; ring
  exact (by simpa only [hScalar,one_smul] using
    (sub_smul (((k+1 : ℕ) : ℝ)) (k : ℝ)
      (sphereSobolevSingleL (-(1/2 : ℝ)) (k+1) (harmonicDerivativeAdjoint hF k a u))))

/-- The physical-degree lowering gain is -a, including the literal degree-zero kernel. -/
theorem degreeLoweringHigh_graph (a : Fin 3) :
    (JL).comp (-aH a) = (BL).comp (aH a)-(aL a).comp BH := by
  apply sphereSobolev_clm_eq_of_single (3/2 : ℝ)
  intro k u
  cases k with
  | zero =>
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply,
      loweringHigh_single_zero,loweringLow_single_zero,degreeHigh_single,Nat.cast_zero,
      zero_smul,map_zero,neg_zero,sub_self]
  | succ k =>
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply,
      loweringHigh_single_succ,loweringLow_single_succ,degreeHigh_single,degreeLow_single,
      map_smul,map_neg,sphereSobolevInclusionL_single]
    have hScalar : ((k : ℝ)-((k+1 : ℕ) : ℝ)) = -1 := by push_cast; ring
    exact (by simpa only [hScalar,neg_one_smul] using
      (sub_smul (k : ℝ) (((k+1 : ℕ) : ℝ))
        (sphereSobolevSingleL (-(1/2 : ℝ)) k (harmonicDerivative hF k a u))))

/-- Independently defined actual low rotation gains are compatible with the high maps. -/
theorem rotationRaising_endpoint_compatibility (i j a : Fin 3) :
    (rotationRaisingLow hF hO hD i j a).comp IH=(JL).comp (rotationRaisingHigh hF hO hD i j a) := by
  apply ContinuousLinearMap.ext
  intro u
  have h1 : (if a=j then AL i else 0) (IH u) = JL ((if a=j then AH i else 0) u) := by
    split_ifs
    · exact (v017_inclusion_raisingHigh hF hO hD i u).symm
    · simp only [ContinuousLinearMap.zero_apply,map_zero]
  have h2 : (if a=i then AL j else 0) (IH u) = JL ((if a=i then AH j else 0) u) := by
    split_ifs
    · exact (v017_inclusion_raisingHigh hF hO hD j u).symm
    · simp only [ContinuousLinearMap.zero_apply,map_zero]
  change (if a=j then AL i else 0) (IH u) - (if a=i then AL j else 0) (IH u) =
    JL (((if a=j then AH i else 0) u) - ((if a=i then AH j else 0) u))
  exact (congrArg₂ (fun x y : Neg => x-y) h1 h2).trans (map_sub JL _ _).symm

theorem rotationLowering_endpoint_compatibility (i j a : Fin 3) :
    (rotationLoweringLow hF hO hD i j a).comp IH=(JL).comp (rotationLoweringHigh hF hO hD i j a) := by
  apply ContinuousLinearMap.ext
  intro u
  have h1 : (if a=j then aL i else 0) (IH u) = JL ((if a=j then aH i else 0) u) := by
    split_ifs
    · exact (v017_inclusion_loweringHigh hF hO hD i u).symm
    · simp only [ContinuousLinearMap.zero_apply,map_zero]
  have h2 : (if a=i then aL j else 0) (IH u) = JL ((if a=i then aH j else 0) u) := by
    split_ifs
    · exact (v017_inclusion_loweringHigh hF hO hD j u).symm
    · simp only [ContinuousLinearMap.zero_apply,map_zero]
  change (if a=j then aL i else 0) (IH u) - (if a=i then aL j else 0) (IH u) =
    JL (((if a=j then aH i else 0) u) - ((if a=i then aH j else 0) u))
  exact (congrArg₂ (fun x y : Neg => x-y) h1 h2).trans (map_sub JL _ _).symm

theorem degreeRaising_endpoint_compatibility (a : Fin 3) :
    (AL a).comp IH=(JL).comp (AH a) := by
  apply ContinuousLinearMap.ext
  intro u
  exact (v017_inclusion_raisingHigh hF hO hD a u).symm

theorem degreeLowering_endpoint_compatibility (a : Fin 3) :
    (-aL a).comp IH=(JL).comp (-aH a) := by
  apply ContinuousLinearMap.ext
  intro u
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.neg_apply,map_neg] using
    congrArg (fun z : Neg => -z) (v017_inclusion_loweringHigh hF hO hD a u).symm

private lemma norm_conditional_le {E : Type*} [NormedAddCommGroup E]
    (P : Prop) [Decidable P] (u : E) : ‖(if P then u else 0)‖ ≤ ‖u‖ := by
  by_cases hP : P
  · simp only [hP,ite_true,le_refl]
  · simpa only [hP,ite_false,norm_zero] using norm_nonneg u

/-- Literal full endpoint norm bounds for the two independently defined rotation rows. -/
theorem rotationRaising_norm_bounds (i j a : Fin 3) :
    ‖rotationRaisingHigh hF hO hD i j a‖ ≤ ‖AH i‖+‖AH j‖ ∧
    ‖rotationRaisingLow hF hO hD i j a‖ ≤ ‖AL i‖+‖AL j‖ := by
  constructor
  · change ‖((if a=j then AH i else 0) - (if a=i then AH j else 0) : Hi →L[ℝ] Half)‖ ≤ _
    have h1 : ‖(if a=j then AH i else 0)‖ ≤ ‖AH i‖ := norm_conditional_le (a=j) (AH i)
    have h2 : ‖(if a=i then AH j else 0)‖ ≤ ‖AH j‖ := norm_conditional_le (a=i) (AH j)
    have hsub : ‖((if a=j then AH i else 0) - (if a=i then AH j else 0) : Hi →L[ℝ] Half)‖ ≤
        ‖(if a=j then AH i else 0)‖ + ‖(if a=i then AH j else 0)‖ := norm_sub_le (if a=j then AH i else 0) (if a=i then AH j else 0)
    exact hsub.trans (add_le_add h1 h2)
  · change ‖((if a=j then AL i else 0) - (if a=i then AL j else 0) : Half →L[ℝ] Neg)‖ ≤ _
    have h1 : ‖(if a=j then AL i else 0)‖ ≤ ‖AL i‖ := norm_conditional_le (a=j) (AL i)
    have h2 : ‖(if a=i then AL j else 0)‖ ≤ ‖AL j‖ := norm_conditional_le (a=i) (AL j)
    have hsub : ‖((if a=j then AL i else 0) - (if a=i then AL j else 0) : Half →L[ℝ] Neg)‖ ≤
        ‖(if a=j then AL i else 0)‖ + ‖(if a=i then AL j else 0)‖ := norm_sub_le (if a=j then AL i else 0) (if a=i then AL j else 0)
    exact hsub.trans (add_le_add h1 h2)

theorem rotationLowering_norm_bounds (i j a : Fin 3) :
    ‖rotationLoweringHigh hF hO hD i j a‖ ≤ ‖aH i‖+‖aH j‖ ∧
    ‖rotationLoweringLow hF hO hD i j a‖ ≤ ‖aL i‖+‖aL j‖ := by
  constructor
  · change ‖((if a=j then aH i else 0) - (if a=i then aH j else 0) : Hi →L[ℝ] Half)‖ ≤ _
    have h1 : ‖(if a=j then aH i else 0)‖ ≤ ‖aH i‖ := norm_conditional_le (a=j) (aH i)
    have h2 : ‖(if a=i then aH j else 0)‖ ≤ ‖aH j‖ := norm_conditional_le (a=i) (aH j)
    have hsub : ‖((if a=j then aH i else 0) - (if a=i then aH j else 0) : Hi →L[ℝ] Half)‖ ≤
        ‖(if a=j then aH i else 0)‖ + ‖(if a=i then aH j else 0)‖ := norm_sub_le (if a=j then aH i else 0) (if a=i then aH j else 0)
    exact hsub.trans (add_le_add h1 h2)
  · change ‖((if a=j then aL i else 0) - (if a=i then aL j else 0) : Half →L[ℝ] Neg)‖ ≤ _
    have h1 : ‖(if a=j then aL i else 0)‖ ≤ ‖aL i‖ := norm_conditional_le (a=j) (aL i)
    have h2 : ‖(if a=i then aL j else 0)‖ ≤ ‖aL j‖ := norm_conditional_le (a=i) (aL j)
    have hsub : ‖((if a=j then aL i else 0) - (if a=i then aL j else 0) : Half →L[ℝ] Neg)‖ ≤
        ‖(if a=j then aL i else 0)‖ + ‖(if a=i then aL j else 0)‖ := norm_sub_le (if a=j then aL i else 0) (if a=i then aL j else 0)
    exact hsub.trans (add_le_add h1 h2)

/-- The actual generator/angular gained maps are constant smooth parameter families. -/
theorem contDiff_rotation_angular {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (i j a : Fin 3) :
    ContDiff ℝ ∞ (fun _ : P => rotationRaisingHigh hF hO hD i j a) ∧
    ContDiff ℝ ∞ (fun _ : P => rotationRaisingLow hF hO hD i j a) ∧
    ContDiff ℝ ∞ (fun _ : P => rotationLoweringHigh hF hO hD i j a) ∧
    ContDiff ℝ ∞ (fun _ : P => rotationLoweringLow hF hO hD i j a) :=
  ⟨contDiff_const,contDiff_const,contDiff_const,contDiff_const⟩

/-- Physical-degree angular gains are constant families at both actual endpoints. -/
theorem contDiff_degree_angular {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (a : Fin 3) :
    ContDiff ℝ ∞ (fun _ : P => AH a) ∧ ContDiff ℝ ∞ (fun _ : P => AL a) ∧
    ContDiff ℝ ∞ (fun _ : P => -aH a) ∧ ContDiff ℝ ∞ (fun _ : P => -aL a) :=
  ⟨contDiff_const,contDiff_const,contDiff_const,contDiff_const⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualCanonicalGeneratorAngularGainedRows
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualCanonicalGeneratorAngularGainedRows.rotationRaisingHigh_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualCanonicalGeneratorAngularGainedRows.rotationLoweringHigh_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualCanonicalGeneratorAngularGainedRows.degreeRaisingHigh_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualCanonicalGeneratorAngularGainedRows.degreeLoweringHigh_graph
