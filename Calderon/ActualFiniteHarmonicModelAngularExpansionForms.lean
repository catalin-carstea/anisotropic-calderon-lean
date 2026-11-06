import Calderon.ActualFiniteHarmonicModelScalarExpansion
import Calderon.ActualFiniteHarmonicModelAngularPolynomialCommutatorForms
import Calderon.ActualFiniteHarmonicModelAngularPolynomialProductForms

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph ActualModelCommutatorWords
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev angularExpansionFormsFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] angularExpansionFormsFunction

lemma coreAngularExpansion_quadratic_linear_commutator_bound
    (hF : SphereFischerInner)
    (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C D : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD (fun p : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF p.1*coreAngularGenerator hO hD hF p.2) A x C)
    (hB : HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF) B x D)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    |⟪commutator A B F x,G x⟫_ℝ| ≤ (C*D)*
      ((8*(coreAngularGeneratorBound hO hD)^2)*‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖) := by
  have hC := hasCoreScalarExpansionBound_nonneg hO hD _ A x C hA
  have hM := (coreAngularGeneratorBound_bounds hO hD).1
  obtain ⟨c,hc,hec,hbc⟩ := hA
  obtain ⟨d,hd,hed,hbd⟩ := hB
  have ht := coreAngular_quadratic_linear_polynomial_commutator_bound hO hD hF
    Finset.univ Finset.univ Prod.fst Prod.snd id c d hc hd F G x
  rw [hec,hed]
  dsimp only [coreScalarCombination,id] at ht ⊢
  with_reducible apply ht.trans
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul hbc hbd (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hC
  · have hM0 : 0 ≤ coreAngularGeneratorBound hO hD := by linarith
    positivity

lemma coreAngularExpansion_quadratic_quadratic_commutator_bound
    (hF : SphereFischerInner)
    (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C D : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD (fun p : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF p.1*coreAngularGenerator hO hD hF p.2) A x C)
    (hB : HasCoreScalarExpansionBound hO hD (fun p : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF p.1*coreAngularGenerator hO hD hF p.2) B x D)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    |⟪commutator A B F x,G x⟫_ℝ| ≤ (C*D)*
      ((16*(coreAngularGeneratorBound hO hD)^3)*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖) := by
  have hC := hasCoreScalarExpansionBound_nonneg hO hD _ A x C hA
  have hM := (coreAngularGeneratorBound_bounds hO hD).1
  obtain ⟨c,hc,hec,hbc⟩ := hA
  obtain ⟨d,hd,hed,hbd⟩ := hB
  have ht := coreAngular_quadratic_quadratic_polynomial_commutator_bound hO hD hF
    Finset.univ Finset.univ Prod.fst Prod.snd Prod.fst Prod.snd c d hc hd F G x
  rw [hec,hed]
  dsimp only [coreScalarCombination,id] at ht ⊢
  with_reducible apply ht.trans
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul hbc hbd (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hC
  · have hM0 : 0 ≤ coreAngularGeneratorBound hO hD := by linarith
    positivity

lemma coreAngularExpansion_linear_quadratic_product_bound
    (hF : SphereFischerInner)
    (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C D : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF) A x C)
    (hB : HasCoreScalarExpansionBound hO hD (fun p : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF p.1*coreAngularGenerator hO hD hF p.2) B x D)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    |⟪(A*B) F x,G x⟫_ℝ| ≤ (C*D)*
      ((coreAngularGeneratorBound hO hD)^3*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖) := by
  have hC := hasCoreScalarExpansionBound_nonneg hO hD _ A x C hA
  have hM := (coreAngularGeneratorBound_bounds hO hD).1
  obtain ⟨c,hc,hec,hbc⟩ := hA
  obtain ⟨d,hd,hed,hbd⟩ := hB
  have ht := coreAngular_linear_quadratic_polynomial_product_bound hO hD hF
    Finset.univ Finset.univ id Prod.fst Prod.snd c d hc hd F G x
  rw [hec,hed]
  dsimp only [coreScalarCombination,id] at ht ⊢
  with_reducible apply ht.trans
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul hbc hbd (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hC
  · have hM0 : 0 ≤ coreAngularGeneratorBound hO hD := by linarith
    positivity

lemma coreAngularExpansion_quadratic_linear_product_bound
    (hF : SphereFischerInner)
    (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD)) (x : R3) (C D : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD (fun p : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF p.1*coreAngularGenerator hO hD hF p.2) A x C)
    (hB : HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF) B x D)
    (F G : smoothCompactFiniteSphereCore hO hD) :
    |⟪(A*B) F x,G x⟫_ℝ| ≤ (C*D)*
      ((coreAngularGeneratorBound hO hD)^3*‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖ *
        ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) G x‖) := by
  have hC := hasCoreScalarExpansionBound_nonneg hO hD _ A x C hA
  have hM := (coreAngularGeneratorBound_bounds hO hD).1
  obtain ⟨c,hc,hec,hbc⟩ := hA
  obtain ⟨d,hd,hed,hbd⟩ := hB
  have ht := coreAngular_quadratic_linear_polynomial_product_bound hO hD hF
    Finset.univ Finset.univ Prod.fst Prod.snd id c d hc hd F G x
  rw [hec,hed]
  dsimp only [coreScalarCombination,id] at ht ⊢
  with_reducible apply ht.trans
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul hbc hbd (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hC
  · have hM0 : 0 ≤ coreAngularGeneratorBound hO hD := by linarith
    positivity

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
