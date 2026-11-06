import Calderon.ActualFiniteHarmonicModelRotationLieCommutator
import Calderon.ActualFiniteHarmonicModelConnectionCommutator

set_option autoImplicit false
noncomputable section
open Set MvPolynomial
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  ActualFiniteHarmonicCore AngularShiftGraph HarmonicDerivativeOperator SmoothSphereRotationProjection
  RotationCasimir
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeRotationShiftFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeRotationShiftFunction

lemma polynomialRotation_pderiv_commutator (i j a : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    polynomialRotation i j (pderiv a p)-pderiv a (polynomialRotation i j p) =
      (if a=j then pderiv i p else 0)-(if a=i then pderiv j p else 0) := by
  classical
  simp only [polynomialRotation,map_sub,pderiv_mul,pderiv_X,Pi.single_apply]
  rw [AngularPolynomial.pderiv_pderiv_comm a j,AngularPolynomial.pderiv_pderiv_comm a i]
  by_cases haj : a=j <;> by_cases hai : a=i <;>
    simp_all only [eq_comm,ite_true,ite_false,mul_zero,mul_one,zero_mul,one_mul] <;> ring


lemma harmonicSphereRotation_derivative_commutator
    (hF : SphereFischerInner) (k : ℕ) (i j a : Fin 3) (u : harmonicSphereSubspace (k+1)) :
    harmonicSphereRotation k i j (harmonicDerivative hF k a u) -
      harmonicDerivative hF k a (harmonicSphereRotation (k+1) i j u) =
      (if a=j then harmonicDerivative hF k i u else 0) -
      (if a=i then harmonicDerivative hF k j u else 0) := by
  rcases harmonicPolynomialSphereMap_surjective (k+1) u with ⟨p,rfl⟩
  have hRot (n : ℕ) (s t : Fin 3) (q : harmonicHomogeneous n) :
      harmonicSphereRotation n s t (harmonicPolynomialSphereMap n q) =
        harmonicPolynomialSphereMap n
          ⟨polynomialRotation s t q,polynomialRotation_harmonic_all n s t q q.property⟩ := by
    rw [harmonicSphereRotation_apply_image]
    rfl
  have hDerivative (b : Fin 3) (q : harmonicHomogeneous (k+1)) :
      harmonicDerivative hF k b (harmonicPolynomialSphereMap (k+1) q) =
        harmonicPolynomialSphereMap k
          ⟨pderiv b (q : MvPolynomial (Fin 3) ℝ),pderiv_harmonicHomogeneous_succ k b q q.property⟩ := by
    rw [harmonicDerivative_apply_image]
    rfl
  simp only [hRot,hDerivative]
  apply Subtype.ext
  have hVal (P : Prop) [Decidable P] (z : harmonicSphereSubspace k) :
      ((if P then z else 0) : harmonicSphereSubspace k).val=(if P then z.val else 0) := by
    by_cases hP : P <;> simp only [hP,ite_true,ite_false,Submodule.coe_zero]
  have hPolyI (P : Prop) [Decidable P] (z : MvPolynomial (Fin 3) ℝ) :
      polynomialSphereL2 (if P then z else 0)=(if P then polynomialSphereL2 z else 0) := by
    by_cases hP : P <;> simp only [hP,ite_true,ite_false,map_zero]
  simpa only [Submodule.coe_sub,Submodule.coe_zero,hVal,hPolyI,
    harmonicPolynomialSphereMap,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,map_sub,map_zero] using
    congrArg polynomialSphereL2 (polynomialRotation_pderiv_commutator i j a p)


lemma harmonicSphereRotation_raising_commutator
    (hF : SphereFischerInner) (k : ℕ) (i j a : Fin 3) (u : harmonicSphereSubspace k) :
    harmonicSphereRotation (k+1) i j (harmonicDerivativeAdjoint hF k a u) -
      harmonicDerivativeAdjoint hF k a (harmonicSphereRotation k i j u) =
      (if a=j then harmonicDerivativeAdjoint hF k i u else 0) -
      (if a=i then harmonicDerivativeAdjoint hF k j u else 0) := by
  apply ext_inner_right ℝ
  intro v
  have he := congrArg (fun z : harmonicSphereSubspace k => ⟪u,z⟫_ℝ)
    (harmonicSphereRotation_derivative_commutator hF k i j a v)
  have hs := inner_harmonicSphereRotation_skew k i j u (harmonicDerivative hF k a v)
  have ht := inner_harmonicSphereRotation_skew (k+1) i j (harmonicDerivativeAdjoint hF k a u) v
  rw [inner_harmonicDerivativeAdjoint] at ht
  have hConditionalAdjunction (P : Prop) [Decidable P] (b : Fin 3) :
      ⟪(if P then harmonicDerivativeAdjoint hF k b u else 0),v⟫_ℝ =
        ⟪u,(if P then harmonicDerivative hF k b v else 0)⟫_ℝ := by
    by_cases hP : P <;>
      simp only [hP,ite_true,ite_false,inner_zero_left,inner_zero_right,inner_harmonicDerivativeAdjoint]
  by_cases haj : a=j <;> by_cases hai : a=i <;>
    (try simp only [haj,hai] at hs ht) <;>
    simp only [haj,hai,ite_true,ite_false,inner_sub_right,inner_zero_right] at he <;>
    simp only [haj,hai,ite_true,ite_false,inner_sub_left,inner_zero_left,
      hConditionalAdjunction,inner_harmonicDerivativeAdjoint] <;> linarith


lemma coreRotation_derivative_commutator
    (hF : SphereFischerInner) (i j a : Fin 3) :
    ActualModelCommutatorWords.commutator (coreRotation hO hD i j) (coreDerivative hO hD hF a) =
      (if a=j then coreDerivative hO hD hF i else 0) -
      (if a=i then coreDerivative hO hD hF j else 0) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  have hEval (P : Prop) [Decidable P] (T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) :
      (if P then T else 0) F x=(if P then T F x else 0) := by
    by_cases hP : P <;> simp only [hP,ite_true,ite_false,LinearMap.zero_apply,Submodule.coe_zero,Pi.zero_apply]
  change coreRotation hO hD i j (coreDerivative hO hD hF a F) x-
      coreDerivative hO hD hF a (coreRotation hO hD i j F) x = _
  simp only [LinearMap.sub_apply,Submodule.coe_sub,Pi.sub_apply,hEval]
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext n
  change sphereHarmonicCoordinate hO hD n
      (coreRotation hO hD i j (coreDerivative hO hD hF a F) x-
        coreDerivative hO hD hF a (coreRotation hO hD i j F) x) =
    sphereHarmonicCoordinate hO hD n
      ((if a=j then coreDerivative hO hD hF i F x else 0)-
        (if a=i then coreDerivative hO hD hF j F x else 0))
  have hRot (q : ℕ) (U : smoothCompactFiniteSphereCore hO hD) :
      sphereHarmonicCoordinate hO hD q (coreRotation hO hD i j U x) =
        harmonicSphereRotation q i j (sphereHarmonicCoordinate hO hD q (U x)) :=
    coreBlockOperator_coordinate hO hD (fun k => harmonicSphereRotation k i j) U x q
  have hcI (P : Prop) [Decidable P] (z : SphereL2) :
      sphereHarmonicCoordinate hO hD n (if P then z else 0)=
        (if P then sphereHarmonicCoordinate hO hD n z else 0) := by
    by_cases hP : P <;> simp only [hP,ite_true,ite_false,map_zero]
  simp only [map_sub,hcI]
  rw [hRot n (coreDerivative hO hD hF a F),coreDerivative_graph hO hD hF a F x n,
    coreDerivative_graph hO hD hF a (coreRotation hO hD i j F) x n,hRot (n+1) F]
  simp only [coreDerivative_graph hO hD hF _ F x n]
  exact harmonicSphereRotation_derivative_commutator hF n i j a
    (sphereHarmonicCoordinate hO hD (n+1) (F x))


lemma coreRotation_raising_commutator
    (hF : SphereFischerInner) (i j a : Fin 3) :
    ActualModelCommutatorWords.commutator (coreRotation hO hD i j) (coreRaising hO hD hF a) =
      (if a=j then coreRaising hO hD hF i else 0) -
      (if a=i then coreRaising hO hD hF j else 0) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  have hEval (P : Prop) [Decidable P] (T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) :
      (if P then T else 0) F x=(if P then T F x else 0) := by
    by_cases hP : P <;> simp only [hP,ite_true,ite_false,LinearMap.zero_apply,Submodule.coe_zero,Pi.zero_apply]
  change coreRotation hO hD i j (coreRaising hO hD hF a F) x-
      coreRaising hO hD hF a (coreRotation hO hD i j F) x = _
  simp only [LinearMap.sub_apply,Submodule.coe_sub,Pi.sub_apply,hEval]
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext n
  change sphereHarmonicCoordinate hO hD n
      (coreRotation hO hD i j (coreRaising hO hD hF a F) x-
        coreRaising hO hD hF a (coreRotation hO hD i j F) x) =
    sphereHarmonicCoordinate hO hD n
      ((if a=j then coreRaising hO hD hF i F x else 0)-
        (if a=i then coreRaising hO hD hF j F x else 0))
  have hRot (q : ℕ) (U : smoothCompactFiniteSphereCore hO hD) :
      sphereHarmonicCoordinate hO hD q (coreRotation hO hD i j U x) =
        harmonicSphereRotation q i j (sphereHarmonicCoordinate hO hD q (U x)) :=
    coreBlockOperator_coordinate hO hD (fun k => harmonicSphereRotation k i j) U x q
  have hcI (P : Prop) [Decidable P] (z : SphereL2) :
      sphereHarmonicCoordinate hO hD n (if P then z else 0)=
        (if P then sphereHarmonicCoordinate hO hD n z else 0) := by
    by_cases hP : P <;> simp only [hP,ite_true,ite_false,map_zero]
  simp only [map_sub,hcI]
  cases n with
  | zero =>
    rw [hRot 0 (coreRaising hO hD hF a F),(coreRaising_graph hO hD hF a F x).1,
      (coreRaising_graph hO hD hF a (coreRotation hO hD i j F) x).1,map_zero,sub_zero]
    simp only [(coreRaising_graph hO hD hF _ F x).1,ite_self,sub_self]
  | succ k =>
    rw [hRot (k+1) (coreRaising hO hD hF a F),(coreRaising_graph hO hD hF a F x).2 k,
      (coreRaising_graph hO hD hF a (coreRotation hO hD i j F) x).2 k,hRot k F]
    simp only [(coreRaising_graph hO hD hF _ F x).2 k]
    exact harmonicSphereRotation_raising_commutator hF k i j a
      (sphereHarmonicCoordinate hO hD k (F x))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
