import Calderon.ActualAngularPiMixedLowInstantiationDraft
import Calderon.SphereSobolevAngularRaisingSingle
import Calderon.ActualAngularCommutatorHalfForm
import Calderon.SectionFiveErrorForms

/-! Sol author candidate. Upfront: before-canonical-bracket-v001/MATHEMATICS.md.
Literal canonical [a_i,A_j] graph and independently constructed Hi/Half endpoints.
Physical degree remains k; normalization of the historical bounded operator is k+1.
No compiler run or semantic acceptance is claimed. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualCanonicalAngularGainedBracket
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  HarmonicDerivativeOperator BoundedAngularShift BoundedSpectralMultiplier
  ActualAngularDerivativeRaisingCommutator ActualAngularPolynomialCommutator
  ActualAngularHighDraft ActualAngularPiDraft
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

/-- The raw degree-preserving bracket, including its genuine constant-mode block. -/
def harmonicBracketBlock (i j : Fin 3) : (k : ℕ) →
    harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k
  | 0 => (harmonicDerivative hF 0 i).comp (harmonicDerivativeAdjoint hF 0 j)
  | m+1 => (harmonicDerivative hF (m+1) i).comp (harmonicDerivativeAdjoint hF (m+1) j) -
      (harmonicDerivativeAdjoint hF m j).comp (harmonicDerivative hF m i)

/-- The actual historical normalized bracket satisfies its exact k+1 normalization. -/
lemma normalized_bracket_coefficient (i j : Fin 3) (u : SphereL2) (k : ℕ) :
    (1+(k : ℝ)) • sphereHarmonicCoordinate hO hD k
      (normalizedDerivativeRaisingCommutator hF hO hD i j u) =
    harmonicBracketBlock hF i j k (sphereHarmonicCoordinate hO hD k u) := by
  have hM1 (v : SphereL2) (l : ℕ) : sphereHarmonicCoordinate hO hD l
      (derivativeRaisingFirstMultiplier hO hD v) =
      derivativeRaisingFirstWeight l • sphereHarmonicCoordinate hO hD l v :=
    boundedSpectralMultiplier_mem hO hD _ 1 (by norm_num) abs_derivativeRaisingFirstWeight_le_one v l
  have hM2 (v : SphereL2) (l : ℕ) : sphereHarmonicCoordinate hO hD l
      (derivativeRaisingSecondMultiplier hO hD v) =
      derivativeRaisingSecondWeight l • sphereHarmonicCoordinate hO hD l v :=
    boundedSpectralMultiplier_mem hO hD _ 2 (by norm_num) abs_derivativeRaisingSecondWeight_le_two v l
  have hz (a b : Fin 3) (v : SphereL2) : sphereHarmonicCoordinate hO hD 0
      (normalizedRaising hF hO hD a (normalizedDerivative hF hO hD b v)) = 0 :=
    (normalizedRaisingOutput_graph hF hO hD a (normalizedDerivative hF hO hD b v)).1
  cases k with
  | zero =>
    have hRaw := harmonicDerivativeAdjoint_zero_commutator hF i j (sphereHarmonicCoordinate hO hD 0 u)
    by_cases hij : i=j
    · simp only [normalizedDerivativeRaisingCommutator,hij,ite_true,
        ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,map_add,map_sub,map_smul,
        hM1,hM2,hz,inverseDegreeMultiplier_coordinate,inverseDegreeWeight,Nat.cast_zero,
        zero_add,add_zero,inv_one,one_smul,smul_zero,sub_zero,harmonicBracketBlock,
        harmonicDerivativeAdjoint_zero_commutator,ite_true]
      module
    · simp only [normalizedDerivativeRaisingCommutator,hij,ite_false,
        ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.zero_apply,map_add,map_sub,map_zero,hM1,hM2,hz,smul_zero,
        zero_add,sub_zero,harmonicBracketBlock,harmonicDerivativeAdjoint_zero_commutator,ite_false]
  | succ m =>
    have hDiag : (1+((m+1 : ℕ) : ℝ))*(2+inverseDegreeWeight (m+1)) = 2*(m : ℝ)+5 := by
      unfold inverseDegreeWeight
      push_cast
      field_simp
      <;> ring
    have hFirst : (1+((m+1 : ℕ) : ℝ))*derivativeRaisingFirstWeight (m+1)*
        (inverseDegreeWeight m*inverseDegreeWeight (m+1)) = 2/(2*(m : ℝ)+3) := by
      unfold derivativeRaisingFirstWeight inverseDegreeWeight
      push_cast
      field_simp
      <;> ring
    have hSecond : (1+((m+1 : ℕ) : ℝ))*derivativeRaisingSecondWeight (m+1)*
        (inverseDegreeWeight m*inverseDegreeWeight (m+1)) =
        2*(2*(m : ℝ)+5)/(2*(m : ℝ)+3)^2 := by
      unfold derivativeRaisingSecondWeight inverseDegreeWeight
      push_cast
      field_simp
      <;> ring
    have hRaw := harmonicDerivativeAdjoint_commutator hF m i j
      (sphereHarmonicCoordinate hO hD (m+1) u)
    change _ = harmonicDerivative hF (m+1) i
        (harmonicDerivativeAdjoint hF (m+1) j (sphereHarmonicCoordinate hO hD (m+1) u)) -
      harmonicDerivativeAdjoint hF m j
        (harmonicDerivative hF m i (sphereHarmonicCoordinate hO hD (m+1) u))
    rw [hRaw]
    by_cases hij : i=j
    · simp only [normalizedDerivativeRaisingCommutator,hij,ite_true,
        ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,map_add,map_sub,map_smul,
        hM1,hM2,inverseDegreeMultiplier_coordinate,normalizedRaising_derivative_coordinate,
        smul_add,smul_sub,smul_smul,← add_smul]
      rw [hDiag]
      simp only [mul_assoc] at hFirst hSecond
      rw [hFirst,hSecond]
    · simp only [normalizedDerivativeRaisingCommutator,hij,ite_false,
        ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.zero_apply,map_add,map_sub,map_zero,hM1,hM2,
        normalizedRaising_derivative_coordinate,smul_add,smul_sub,smul_smul,smul_zero,zero_add]
      simp only [mul_assoc] at hFirst hSecond
      rw [hFirst,hSecond]

/-- This is an operator on full canonical completions. Its order is certified by
its physical single formula below, not by the common normalized carrier. -/
def gainedAtOrder (s : ℝ) (i j : Fin 3) : SphereSobolev s →L[ℝ] SphereSobolev (s-1) :=
  (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((normalizedDerivativeRaisingCommutator hF hO hD i j).comp
      (sphereSobolevZeroEquiv hO hD).symm.toContinuousLinearEquiv.toContinuousLinearMap)

lemma norm_gainedAtOrder_le (s : ℝ) (i j : Fin 3) :
    ‖gainedAtOrder hF hO hD s i j‖ ≤ 15 := by
  refine (gainedAtOrder hF hO hD s i j).opNorm_le_bound (by norm_num) ?_
  intro u
  change ‖sphereSobolevZeroEquiv hO hD
    (normalizedDerivativeRaisingCommutator hF hO hD i j ((sphereSobolevZeroEquiv hO hD).symm u))‖ ≤ 15*‖u‖
  rw [LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using
    (normalizedDerivativeRaisingCommutator hF hO hD i j).le_of_opNorm_le
      (norm_normalizedDerivativeRaisingCommutator_le hF hO hD i j)
      ((sphereSobolevZeroEquiv hO hD).symm u)

private lemma besselWeight_order_step (s : ℝ) (k : ℕ) :
    besselWeight s k = (1+(k : ℝ))*besselWeight (s-1) k := by
  have h := SectionFiveErrorForms.besselWeight_add (s-1) 1 k
  have hs : s-1+1 = s := by ring
  rw [hs] at h
  simpa only [besselWeight,Real.rpow_one,mul_comm] using h

lemma gainedAtOrder_single (s : ℝ) (i j : Fin 3) (k : ℕ)
    (u : harmonicSphereSubspace k) :
    gainedAtOrder hF hO hD s i j (sphereSobolevSingleL s k u) =
      sphereSobolevSingleL (s-1) k (harmonicBracketBlock hF i j k u) := by
  let Z := sphereSobolevZeroEquiv hO hD
  let v : SphereL2 := Z.symm (sphereSobolevSingleL s k u)
  apply lp.ext
  funext l
  have hNorm := normalized_bracket_coefficient hF hO hD i j v l
  have hCoords : sphereHarmonicCoordinate hO hD l v =
      (sphereSobolevSingleL s k u) l := by
    change (Z v) l = _
    exact congrArg (fun z : SphereSobolev 0 => z l) (Z.apply_symm_apply _)
  have hValue : (gainedAtOrder hF hO hD s i j (sphereSobolevSingleL s k u)) l =
      sphereHarmonicCoordinate hO hD l (normalizedDerivativeRaisingCommutator hF hO hD i j v) := rfl
  rw [hCoords] at hNorm
  rw [hValue]
  by_cases hl : l=k
  · subst l
    have hInput : (sphereSobolevSingleL s k u) k = besselWeight s k • u := by
      change besselWeight s k • (lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 k u) k = _
      rw [lp.single_apply_self]
    have hOutput : (sphereSobolevSingleL (s-1) k (harmonicBracketBlock hF i j k u)) k =
        besselWeight (s-1) k • harmonicBracketBlock hF i j k u := by
      change besselWeight (s-1) k •
        (lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 k (harmonicBracketBlock hF i j k u)) k = _
      rw [lp.single_apply_self]
    have hScaled : (1+(k : ℝ)) • sphereHarmonicCoordinate hO hD k
        (normalizedDerivativeRaisingCommutator hF hO hD i j v) =
        (1+(k : ℝ)) • (besselWeight (s-1) k • harmonicBracketBlock hF i j k u) := by
      simpa only [hInput,map_smul,besselWeight_order_step s k,smul_smul] using hNorm
    rw [hOutput]
    exact smul_right_injective (harmonicSphereSubspace k)
      (show 1+(k : ℝ) ≠ 0 by positivity) hScaled
  · have hInput : (sphereSobolevSingleL s k u) l = 0 := by
      change besselWeight s k • (lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 k u) l = 0
      rw [lp.single_apply_ne (E := fun n : ℕ => harmonicSphereSubspace n) 2 k u hl,smul_zero]
    have hOutput : (sphereSobolevSingleL (s-1) k (harmonicBracketBlock hF i j k u)) l = 0 := by
      change besselWeight (s-1) k •
        (lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 k (harmonicBracketBlock hF i j k u)) l = 0
      rw [lp.single_apply_ne (E := fun n : ℕ => harmonicSphereSubspace n) 2 k _ hl,smul_zero]
    rw [hInput,map_zero] at hNorm
    rw [hOutput]
    exact (smul_eq_zero.mp hNorm).resolve_left (by positivity)

private lemma single_order_congr (s t : ℝ) (hst : s=t) (k : ℕ) (v : harmonicSphereSubspace k) :
    sphereSobolevSingleL s k v = sphereSobolevSingleL t k v := by
  subst t
  rfl

private lemma gainedHigh_single (i j : Fin 3) (k : ℕ) (v : harmonicSphereSubspace k) :
    gainedAtOrder hF hO hD (3/2 : ℝ) i j (sphereSobolevSingleL (3/2 : ℝ) k v) =
      sphereSobolevSingleL (1/2 : ℝ) k (harmonicBracketBlock hF i j k v) :=
  (gainedAtOrder_single hF hO hD (3/2 : ℝ) i j k v).trans
    (single_order_congr _ _ (by norm_num) k _)

private lemma gainedLow_single (i j : Fin 3) (k : ℕ) (v : harmonicSphereSubspace k) :
    gainedAtOrder hF hO hD (1/2 : ℝ) i j (sphereSobolevSingleL (1/2 : ℝ) k v) =
      sphereSobolevSingleL (-(1/2 : ℝ)) k (harmonicBracketBlock hF i j k v) :=
  (gainedAtOrder_single hF hO hD (1/2 : ℝ) i j k v).trans
    (single_order_congr _ _ (by norm_num) k _)

private lemma raisingHigh_single (i : Fin 3) (k : ℕ) (u : harmonicSphereSubspace k) :
    raisingHigh hF hO hD i (sphereSobolevSingleL (3/2 : ℝ) k u) =
      sphereSobolevSingleL (1/2 : ℝ) (k+1) (harmonicDerivativeAdjoint hF k i u) := by
  have h := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (3/2 : ℝ) i k u
  simpa only [raisingHigh,sphereSobolevAngularCoordinateTransposeL,sphereSobolevSingleL,
    ContinuousLinearMap.smul_apply,lp.singleContinuousLinearMap_apply,
    show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num] using h

private lemma raisingLow_single (i : Fin 3) (k : ℕ) (u : harmonicSphereSubspace k) :
    raisingLow hF hO hD i (sphereSobolevSingleL (1/2 : ℝ) k u) =
      sphereSobolevSingleL (-(1/2 : ℝ)) (k+1) (harmonicDerivativeAdjoint hF k i u) := by
  have h := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (1/2 : ℝ) i k u
  simpa only [raisingLow,sphereSobolevAngularCoordinateTransposeL,sphereSobolevSingleL,
    ContinuousLinearMap.smul_apply,lp.singleContinuousLinearMap_apply,
    show (1/2 : ℝ)-1 = -(1/2 : ℝ) by norm_num] using h

private lemma pairing_single_left (k : ℕ) (u : harmonicSphereSubspace k) (v : Neg) :
    PP (sphereSobolevSingleL (1/2 : ℝ) k u) v =
      ⟪u,sphereSobolevCoefficientL (-(1/2 : ℝ)) k v⟫_ℝ := by
  let vk : harmonicSphereSubspace k := v k
  have hc : sphereSobolevCoefficientL (-(1/2 : ℝ)) k v = besselWeight (1/2 : ℝ) k • vk := by
    change besselWeight (-(-(1/2 : ℝ))) k • vk = _
    rw [neg_neg]
  have hl := real_inner_smul_left
    (F := SphereSobolev (1/2 : ℝ))
    (lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 k u) v (besselWeight (1/2 : ℝ) k)
  have hi := lp.inner_single_left (𝕜 := ℝ) k u v
  calc
    PP (sphereSobolevSingleL (1/2 : ℝ) k u) v =
        besselWeight (1/2 : ℝ) k * ⟪lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 k u,v⟫_ℝ := hl
    _ = besselWeight (1/2 : ℝ) k * ⟪u,vk⟫_ℝ :=
      congrArg (fun r : ℝ => besselWeight (1/2 : ℝ) k * r) hi
    _ = ⟪u,besselWeight (1/2 : ℝ) k • vk⟫_ℝ :=
      (real_inner_smul_right (F := harmonicSphereSubspace k) u vk (besselWeight (1/2 : ℝ) k)).symm
    _ = ⟪u,sphereSobolevCoefficientL (-(1/2 : ℝ)) k v⟫_ℝ := congrArg (fun z => ⟪u,z⟫_ℝ) hc.symm

attribute [local irreducible] loweringLow loweringHigh raisingLow raisingHigh
  sphereSobolevCoefficientL sphereSobolevSingleL gainedAtOrder harmonicBracketBlock

/-- Actual low lowering single, derived from genuine angular adjunction. -/
lemma loweringLow_single_succ (i : Fin 3) (m : ℕ) (u : harmonicSphereSubspace (m+1)) :
    loweringLow hF hO hD i (sphereSobolevSingleL (1/2 : ℝ) (m+1) u) =
      sphereSobolevSingleL (-(1/2 : ℝ)) m (harmonicDerivative hF m i u) := by
  apply sphereSobolev_ext (-(1/2 : ℝ))
  intro n
  apply ext_inner_left ℝ
  intro b
  have hRaw := v017_pairing_loweringLow_raisingLow hF hO hD i
    (sphereSobolevSingleL (1/2 : ℝ) n b) (sphereSobolevSingleL (1/2 : ℝ) (m+1) u)
  have hRight := congrArg (fun z : Neg => PP (sphereSobolevSingleL (1/2 : ℝ) (m+1) u) z)
    (raisingLow_single hF hO hD i n b)
  have hAdj := (pairing_single_left n b _).symm.trans
    (hRaw.trans (hRight.trans (pairing_single_left (m+1) u _)))
  by_cases hn : n=m
  · subst n
    have hc := sphereSobolevCoefficientL_single_self (-(1/2 : ℝ)) (m+1)
      (harmonicDerivativeAdjoint hF m i b)
    have hr := sphereSobolevCoefficientL_single_self (-(1/2 : ℝ)) m (harmonicDerivative hF m i u)
    exact hAdj.trans ((congrArg (fun z : harmonicSphereSubspace (m+1) => ⟪u,z⟫_ℝ) hc).trans
      (((real_inner_comm u (harmonicDerivativeAdjoint hF m i b)).symm.trans
        (inner_harmonicDerivativeAdjoint hF m i b u)).trans
          (congrArg (fun z : harmonicSphereSubspace m => ⟪b,z⟫_ℝ) hr.symm)))
  · have hmn : m+1 ≠ n+1 := by omega
    have hc := sphereSobolevCoefficientL_single_ne (-(1/2 : ℝ)) (n+1) (m+1) hmn
      (harmonicDerivativeAdjoint hF n i b)
    have hr := sphereSobolevCoefficientL_single_ne (-(1/2 : ℝ)) m n hn (harmonicDerivative hF m i u)
    exact hAdj.trans ((congrArg (fun z : harmonicSphereSubspace (m+1) => ⟪u,z⟫_ℝ) hc).trans
      ((inner_zero_right u).trans ((inner_zero_right b).symm.trans
        (congrArg (fun z : harmonicSphereSubspace n => ⟪b,z⟫_ℝ) hr.symm))))

lemma loweringLow_single_zero (i : Fin 3) (u : harmonicSphereSubspace 0) :
    loweringLow hF hO hD i (sphereSobolevSingleL (1/2 : ℝ) 0 u) = 0 := by
  apply sphereSobolev_ext (-(1/2 : ℝ))
  intro n
  apply ext_inner_left ℝ
  intro b
  have hRaw := v017_pairing_loweringLow_raisingLow hF hO hD i
    (sphereSobolevSingleL (1/2 : ℝ) n b) (sphereSobolevSingleL (1/2 : ℝ) 0 u)
  have hRight := congrArg (fun z : Neg => PP (sphereSobolevSingleL (1/2 : ℝ) 0 u) z)
    (raisingLow_single hF hO hD i n b)
  have hAdj := (pairing_single_left n b _).symm.trans
    (hRaw.trans (hRight.trans (pairing_single_left 0 u _)))
  have hc := sphereSobolevCoefficientL_single_ne (-(1/2 : ℝ)) (n+1) 0 (by omega)
    (harmonicDerivativeAdjoint hF n i b)
  have hr : sphereSobolevCoefficientL (-(1/2 : ℝ)) n (0 : Neg) = 0 := map_zero _
  exact hAdj.trans ((congrArg (fun z : harmonicSphereSubspace 0 => ⟪u,z⟫_ℝ) hc).trans
    ((inner_zero_right u).trans ((inner_zero_right b).symm.trans
      (congrArg (fun z : harmonicSphereSubspace n => ⟪b,z⟫_ℝ) hr.symm))))

lemma loweringHigh_single_succ (i : Fin 3) (m : ℕ) (u : harmonicSphereSubspace (m+1)) :
    loweringHigh hF hO hD i (sphereSobolevSingleL (3/2 : ℝ) (m+1) u) =
      sphereSobolevSingleL (1/2 : ℝ) m (harmonicDerivative hF m i u) := by
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  rw [v017_inclusion_loweringHigh hF hO hD i,sphereSobolevInclusionL_single,
    loweringLow_single_succ,sphereSobolevInclusionL_single]

lemma loweringHigh_single_zero (i : Fin 3) (u : harmonicSphereSubspace 0) :
    loweringHigh hF hO hD i (sphereSobolevSingleL (3/2 : ℝ) 0 u) = 0 := by
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  rw [v017_inclusion_loweringHigh hF hO hD i,sphereSobolevInclusionL_single,
    loweringLow_single_zero,map_zero]

/-- Literal full Hi weak graph, with both ordered terms in the true negative endpoint. -/
theorem gainedHigh_graph (i j : Fin 3) (u : Hi) :
    JL (gainedAtOrder hF hO hD (3/2 : ℝ) i j u) =
      loweringLow hF hO hD i (raisingHigh hF hO hD j u) -
        raisingLow hF hO hD j (loweringHigh hF hO hD i u) := by
  let L : Hi →L[ℝ] Neg := (JL).comp (gainedAtOrder hF hO hD (3/2 : ℝ) i j)
  let R : Hi →L[ℝ] Neg := (loweringLow hF hO hD i).comp (raisingHigh hF hO hD j) -
    (raisingLow hF hO hD j).comp (loweringHigh hF hO hD i)
  have hSingle (k : ℕ) (v : harmonicSphereSubspace k) :
      L (sphereSobolevSingleL (3/2 : ℝ) k v) = R (sphereSobolevSingleL (3/2 : ℝ) k v) := by
    cases k with
    | zero =>
      simp only [L,R,ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,
        gainedHigh_single,raisingHigh_single,loweringLow_single_succ,
        loweringHigh_single_zero,map_zero,sub_zero,sphereSobolevInclusionL_single,
        harmonicBracketBlock,
        show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num]
    | succ m =>
      simp only [L,R,ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,
        gainedHigh_single,raisingHigh_single,loweringLow_single_succ,
        loweringHigh_single_succ,raisingLow_single,sphereSobolevInclusionL_single,
        harmonicBracketBlock,map_sub,
        show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num]
  have hFinite (n : ℕ) : L (sphereSobolevPartialSum (3/2 : ℝ) n u) =
      R (sphereSobolevPartialSum (3/2 : ℝ) n u) := by
    simp only [sphereSobolevPartialSum,map_sum]
    exact Finset.sum_congr rfl (fun k _ => hSingle k (sphereSobolevCoefficientL (3/2 : ℝ) k u))
  exact tendsto_nhds_unique
    (((L.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum (3/2 : ℝ) u)).congr'
      (Filter.Eventually.of_forall hFinite))
    ((R.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum (3/2 : ℝ) u))

/-- Independent direct low endpoint compatibility; its own norm cap is 15. -/
theorem gainedHigh_low_compatibility (i j : Fin 3) :
    (gainedAtOrder hF hO hD (1/2 : ℝ) i j).comp IH =
      (JL).comp (gainedAtOrder hF hO hD (3/2 : ℝ) i j) := by
  apply ContinuousLinearMap.ext
  intro u
  let L := (gainedAtOrder hF hO hD (1/2 : ℝ) i j).comp IH
  let R := (JL).comp (gainedAtOrder hF hO hD (3/2 : ℝ) i j)
  have hSingle (k : ℕ) (v : harmonicSphereSubspace k) :
      L (sphereSobolevSingleL (3/2 : ℝ) k v) = R (sphereSobolevSingleL (3/2 : ℝ) k v) := by
    simp only [L,R,ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_single,
      gainedHigh_single,gainedLow_single]
  have hFinite (n : ℕ) : L (sphereSobolevPartialSum (3/2 : ℝ) n u) =
      R (sphereSobolevPartialSum (3/2 : ℝ) n u) := by
    simp only [sphereSobolevPartialSum,map_sum]
    exact Finset.sum_congr rfl (fun k _ => hSingle k (sphereSobolevCoefficientL (3/2 : ℝ) k u))
  exact tendsto_nhds_unique
    (((L.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum (3/2 : ℝ) u)).congr'
      (Filter.Eventually.of_forall hFinite))
    ((R.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum (3/2 : ℝ) u))


/-- The swapped-index adjunction needed by balanced endpoint assembly is proved
from the exact graph and genuine canonical pivots. -/
theorem gainedHigh_swapped_pairing (i j : Fin 3) (u v : Hi) :
    PP (IH v) (JL (gainedAtOrder hF hO hD (3/2 : ℝ) i j u)) =
      PP (IH u) (JL (gainedAtOrder hF hO hD (3/2 : ℝ) j i v)) := by
  have h1 : PP (IH v) (loweringLow hF hO hD i (raisingHigh hF hO hD j u)) =
      PP (IH u) (loweringLow hF hO hD j (raisingHigh hF hO hD i v)) :=
    (v017_aA1 hF hO hD i v (raisingHigh hF hO hD j u)).trans
      ((v016_pairing_inclusion_symm (raisingHigh hF hO hD j u) (raisingHigh hF hO hD i v)).trans
        (v017_aA1 hF hO hD j u (raisingHigh hF hO hD i v)).symm)
  have h2 : PP (IH v) (raisingLow hF hO hD j (loweringHigh hF hO hD i u)) =
      PP (IH u) (raisingLow hF hO hD i (loweringHigh hF hO hD j v)) :=
    (v017_aA2 hF hO hD j v (loweringHigh hF hO hD i u)).symm.trans
      ((v016_pairing_inclusion_symm (loweringHigh hF hO hD j v) (loweringHigh hF hO hD i u)).trans
        (v017_aA2 hF hO hD i u (loweringHigh hF hO hD j v)))
  have hc := congrArg (fun z : Neg => PP (IH v) z) (gainedHigh_graph hF hO hD i j u)
  have hd := congrArg (fun z : Neg => PP (IH u) z) (gainedHigh_graph hF hO hD j i v)
  have hc' := hc.trans (v016_pairing_sub_right (IH v) _ _)
  have hd' := hd.trans (v016_pairing_sub_right (IH u) _ _)
  exact hc'.trans ((congrArg₂ (fun x y : ℝ => x-y) h1 h2).trans hd'.symm)


private theorem balancedLow_exists (Ch Dh : Hi →L[ℝ] Half)
    (hAdj : ∀ u v : Hi, PP (IH v) (JL (Ch u)) = PP (IH u) (JL (Dh v))) :
    ∃ B : Half →L[ℝ] Neg,
      B.comp IH = (JL).comp Ch ∧
      (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp B =
        (v016TransposeL Dh).comp JL ∧
      ‖B‖ ≤ (‖Dh‖+‖Ch‖)/2 := by
  have hc := v016_compatible_of_adjunction Ch Dh hAdj
  let B : Half →L[ℝ] Neg := sphereSobolevBalancedDualEndpointL (v016TransposeL Dh) Ch hc
  have hUp : B.comp IH = (JL).comp Ch :=
    sphereSobolevBalancedDualEndpointL_upper_inclusion (v016TransposeL Dh) Ch hc
  have hLo : (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp B =
      (v016TransposeL Dh).comp JL :=
    sphereSobolevBalancedDualEndpointL_lower_inclusion (v016TransposeL Dh) Ch hc
  have hN0 : ‖B‖ ≤ (‖v016TransposeL Dh‖+‖Ch‖)/2 :=
    norm_sphereSobolevBalancedDualEndpointL_le (v016TransposeL Dh) Ch hc
  have hN1 := norm_v016TransposeL_apply_le Dh
  exact ⟨B,hUp,hLo,hN0.trans (by linarith)⟩

/-- Identification with the actual paired/balanced low construction gives its
full lower weak transpose graph, as in the existing mixed-low instantiation. -/
theorem gainedLow_balanced_weak_graph (i j : Fin 3) :
    (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp
        (gainedAtOrder hF hO hD (1/2 : ℝ) i j) =
      (v016TransposeL (gainedAtOrder hF hO hD (3/2 : ℝ) j i)).comp JL ∧
    ‖gainedAtOrder hF hO hD (1/2 : ℝ) i j‖ ≤
      (‖gainedAtOrder hF hO hD (3/2 : ℝ) j i‖ +
        ‖gainedAtOrder hF hO hD (3/2 : ℝ) i j‖)/2 := by
  let Ch : Hi →L[ℝ] Half := gainedAtOrder hF hO hD (3/2 : ℝ) i j
  let Dh : Hi →L[ℝ] Half := gainedAtOrder hF hO hD (3/2 : ℝ) j i
  let Cl : Half →L[ℝ] Neg := gainedAtOrder hF hO hD (1/2 : ℝ) i j
  have hAdj : ∀ u v : Hi, PP (IH v) (JL (Ch u)) = PP (IH u) (JL (Dh v)) := by
    intro u v
    exact gainedHigh_swapped_pairing hF hO hD i j u v
  have hOwner : ∃ B : Half →L[ℝ] Neg,
      B.comp IH = (JL).comp Ch ∧
      (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp B =
        (v016TransposeL Dh).comp JL ∧ ‖B‖ ≤ (‖Dh‖+‖Ch‖)/2 :=
    balancedLow_exists Ch Dh hAdj
  obtain ⟨B,hB⟩ := hOwner
  have hBoth : B.comp IH = Cl.comp IH :=
    hB.1.trans (gainedHigh_low_compatibility hF hO hD i j).symm
  have hEq : B = Cl := by
    apply ContinuousLinearMap.ext
    intro u
    have hSingle (k : ℕ) (v : harmonicSphereSubspace k) :
        B (sphereSobolevSingleL (1/2 : ℝ) k v) = Cl (sphereSobolevSingleL (1/2 : ℝ) k v) := by
      have h := congrArg (fun A : Hi →L[ℝ] Neg => A (sphereSobolevSingleL (3/2 : ℝ) k v)) hBoth
      simpa only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_single] using h
    have hFinite (n : ℕ) : B (sphereSobolevPartialSum (1/2 : ℝ) n u) =
        Cl (sphereSobolevPartialSum (1/2 : ℝ) n u) := by
      simp only [sphereSobolevPartialSum,map_sum]
      exact Finset.sum_congr rfl (fun k _ => hSingle k (sphereSobolevCoefficientL (1/2 : ℝ) k u))
    exact tendsto_nhds_unique
      (((B.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum (1/2 : ℝ) u)).congr'
        (Filter.Eventually.of_forall hFinite))
      ((Cl.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum (1/2 : ℝ) u))
  rw [hEq] at hB
  exact ⟨hB.2.1,hB.2.2⟩

/-- The actual angular primitive is constant and smooth in every physical parameter. -/
theorem contDiff_const_gainedAtOrder {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (s : ℝ) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun _ : P => gainedAtOrder hF hO hD s i j) := contDiff_const

/-- Both genuine completion endpoints, with independent norm caps and the exact
negative ordered graph; this has no callback or finite-output premise. -/
theorem exists_actual_canonical_gained_bracket_endpoints :
    ∃ Ch : Fin 3 → Fin 3 → Hi →L[ℝ] Half,
    ∃ Cl : Fin 3 → Fin 3 → Half →L[ℝ] Neg,
      (∀ i j, ‖Ch i j‖ ≤ 15 ∧ ‖Cl i j‖ ≤ 15) ∧
      (∀ i j, (Cl i j).comp IH = (JL).comp (Ch i j)) ∧
      (∀ i j u, JL (Ch i j u) =
        loweringLow hF hO hD i (raisingHigh hF hO hD j u) -
          raisingLow hF hO hD j (loweringHigh hF hO hD i u)) ∧
      (∀ i j u v, PP (IH v) (JL (Ch i j u)) = PP (IH u) (JL (Ch j i v))) ∧
      (∀ i j, (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp (Cl i j) =
        (v016TransposeL (Ch j i)).comp JL ∧ ‖Cl i j‖ ≤ (‖Ch j i‖+‖Ch i j‖)/2) := by
  refine ⟨gainedAtOrder hF hO hD (3/2 : ℝ),gainedAtOrder hF hO hD (1/2 : ℝ),
    fun i j => ⟨norm_gainedAtOrder_le hF hO hD _ i j,norm_gainedAtOrder_le hF hO hD _ i j⟩,
    gainedHigh_low_compatibility hF hO hD,gainedHigh_graph hF hO hD,
    gainedHigh_swapped_pairing hF hO hD,gainedLow_balanced_weak_graph hF hO hD⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualCanonicalAngularGainedBracket

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualCanonicalAngularGainedBracket.gainedHigh_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualCanonicalAngularGainedBracket.exists_actual_canonical_gained_bracket_endpoints

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualCanonicalAngularGainedBracket.gainedLow_balanced_weak_graph
