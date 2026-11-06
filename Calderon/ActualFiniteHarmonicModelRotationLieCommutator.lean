import Calderon.ActualFiniteHarmonicCoreRotation
import Calderon.HarmonicRaising

set_option autoImplicit false
noncomputable section
open Set MvPolynomial
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  ActualFiniteHarmonicCore SmoothSphereRotationProjection RotationCasimir
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeRotationLieFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeRotationLieFunction
lemma polynomialCoordinateDerivative_commutator (i j a b : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    X i*pderiv j (X a*pderiv b p)-X a*pderiv b (X i*pderiv j p) =
      (if j=a then X i*pderiv b p else 0) - (if b=i then X a*pderiv j p else 0) := by
  classical
  simp only [pderiv_mul,pderiv_X,Pi.single_apply]
  rw [AngularPolynomial.pderiv_pderiv_comm b j]
  by_cases hja : j=a <;> by_cases hbi : b=i <;>
    simp_all only [eq_comm,ite_true,ite_false,mul_zero,mul_one,zero_mul,one_mul] <;> ring


lemma polynomialRotation_coordinate_commutator_expansion (i j a b : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    polynomialRotation i j (polynomialRotation a b p)-polynomialRotation a b (polynomialRotation i j p) =
      (X i*pderiv j (X a*pderiv b p)-X a*pderiv b (X i*pderiv j p)) -
      (X i*pderiv j (X b*pderiv a p)-X b*pderiv a (X i*pderiv j p)) -
      (X j*pderiv i (X a*pderiv b p)-X a*pderiv b (X j*pderiv i p)) +
      (X j*pderiv i (X b*pderiv a p)-X b*pderiv a (X j*pderiv i p)) := by
  simp only [polynomialRotation,map_sub,mul_sub]
  abel


lemma rotation_delta_collection {E : Type*} [AddCommGroup E]
    (v : Fin 3 → Fin 3 → E) (i j a b : Fin 3) :
    ((if j=a then v i b else 0)-(if b=i then v a j else 0)) -
      ((if j=b then v i a else 0)-(if a=i then v b j else 0)) -
      ((if i=a then v j b else 0)-(if b=j then v a i else 0)) +
      ((if i=b then v j a else 0)-(if a=j then v b i else 0)) =
      (if j=a then v i b-v b i else 0) -
      (if j=b then v i a-v a i else 0) -
      (if i=a then v j b-v b j else 0) +
      (if i=b then v j a-v a j else 0) := by
  classical
  have hSymm (s t : Fin 3) (z : E) : (if s=t then z else 0)=(if t=s then z else 0) := by
    by_cases hst : s=t
    · rw [if_pos hst,if_pos hst.symm]
    · have hts : t≠s := Ne.symm hst
      rw [if_neg hst,if_neg hts]
  have hSplit (s t : Fin 3) (z w : E) :
      (if s=t then z-w else 0)=(if s=t then z else 0)-(if s=t then w else 0) := by
    by_cases hst : s=t <;> simp only [hst,ite_true,ite_false,sub_zero]
  rw [hSymm b i,hSymm a i,hSymm b j,hSymm a j]
  simp only [hSplit]
  abel


lemma polynomialRotation_lie_commutator (i j a b : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    polynomialRotation i j (polynomialRotation a b p) - polynomialRotation a b (polynomialRotation i j p) =
      (if j=a then polynomialRotation i b p else 0) -
      (if j=b then polynomialRotation i a p else 0) -
      (if i=a then polynomialRotation j b p else 0) +
      (if i=b then polynomialRotation j a p else 0) := by
  rw [polynomialRotation_coordinate_commutator_expansion,
    polynomialCoordinateDerivative_commutator i j a b,
    polynomialCoordinateDerivative_commutator i j b a,
    polynomialCoordinateDerivative_commutator j i a b,
    polynomialCoordinateDerivative_commutator j i b a]
  simpa only [polynomialRotation] using
    rotation_delta_collection (fun s t : Fin 3 => X s*pderiv t p) i j a b


lemma harmonicSphereRotation_lie_commutator (n : ℕ) (i j a b : Fin 3) (u : harmonicSphereSubspace n) :
    harmonicSphereRotation n i j (harmonicSphereRotation n a b u) -
      harmonicSphereRotation n a b (harmonicSphereRotation n i j u) =
      (if j=a then harmonicSphereRotation n i b u else 0) -
      (if j=b then harmonicSphereRotation n i a u else 0) -
      (if i=a then harmonicSphereRotation n j b u else 0) +
      (if i=b then harmonicSphereRotation n j a u else 0) := by
  rcases harmonicPolynomialSphereMap_surjective n u with ⟨p,rfl⟩
  have hRot (s t : Fin 3) (q : harmonicHomogeneous n) :
      harmonicSphereRotation n s t (harmonicPolynomialSphereMap n q) =
        harmonicPolynomialSphereMap n
          ⟨polynomialRotation s t q,polynomialRotation_harmonic_all n s t q q.property⟩ := by
    rw [harmonicSphereRotation_apply_image]
    rfl
  simp only [hRot]
  apply Subtype.ext
  have hVal (P : Prop) [Decidable P] (z : harmonicSphereSubspace n) :
      ((if P then z else 0) : harmonicSphereSubspace n).val = (if P then z.val else 0) := by
    by_cases hP : P <;> simp only [hP,ite_true,ite_false,Submodule.coe_zero]
  have hPolyI (P : Prop) [Decidable P] (z : MvPolynomial (Fin 3) ℝ) :
      polynomialSphereL2 (if P then z else 0) = (if P then polynomialSphereL2 z else 0) := by
    by_cases hP : P <;> simp only [hP,ite_true,ite_false,map_zero]
  simpa only [Submodule.coe_sub,Submodule.coe_add,Submodule.coe_zero,hVal,hPolyI,
    harmonicPolynomialSphereMap,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,
    map_sub,map_add,map_zero] using
    congrArg polynomialSphereL2 (polynomialRotation_lie_commutator i j a b p)


lemma coreRotation_lie_commutator (i j a b : Fin 3) :
    ActualModelCommutatorWords.commutator (coreRotation hO hD i j) (coreRotation hO hD a b) =
      (if j=a then coreRotation hO hD i b else 0) -
      (if j=b then coreRotation hO hD i a else 0) -
      (if i=a then coreRotation hO hD j b else 0) +
      (if i=b then coreRotation hO hD j a else 0) := by
  classical
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  have hEval (P : Prop) [Decidable P] (X : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) :
      (if P then X else 0) F x = (if P then X F x else 0) := by
    by_cases hP : P <;> simp only [hP,ite_true,ite_false,LinearMap.zero_apply,Submodule.coe_zero,Pi.zero_apply]
  change (coreRotation hO hD i j (coreRotation hO hD a b F)) x-
      (coreRotation hO hD a b (coreRotation hO hD i j F)) x = _
  simp only [LinearMap.sub_apply,LinearMap.add_apply,Submodule.coe_sub,Submodule.coe_add,
    Pi.sub_apply,Pi.add_apply,hEval]
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext n
  change sphereHarmonicCoordinate hO hD n
      ((coreRotation hO hD i j (coreRotation hO hD a b F)) x-
        (coreRotation hO hD a b (coreRotation hO hD i j F)) x) =
    sphereHarmonicCoordinate hO hD n
      (((if j=a then coreRotation hO hD i b F x else 0)-
        (if j=b then coreRotation hO hD i a F x else 0)-
        (if i=a then coreRotation hO hD j b F x else 0))+
        (if i=b then coreRotation hO hD j a F x else 0))
  have hc (s t : Fin 3) (U : smoothCompactFiniteSphereCore hO hD) :
      sphereHarmonicCoordinate hO hD n (coreRotation hO hD s t U x) =
        harmonicSphereRotation n s t (sphereHarmonicCoordinate hO hD n (U x)) :=
    coreBlockOperator_coordinate hO hD (fun k => harmonicSphereRotation k s t) U x n
  have hcI (P : Prop) [Decidable P] (z : SphereL2) :
      sphereHarmonicCoordinate hO hD n (if P then z else 0) =
        (if P then sphereHarmonicCoordinate hO hD n z else 0) := by
    by_cases hP : P <;> simp only [hP,ite_true,ite_false,map_zero]
  simp only [map_sub,map_add,map_zero,hcI,hc]
  exact harmonicSphereRotation_lie_commutator n i j a b (sphereHarmonicCoordinate hO hD n (F x))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
