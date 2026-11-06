import Calderon.ActualFiniteHarmonicModelPrincipalH0ReversedForms
import Calderon.SectionFiveErrorForms

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore ActualModelCommutatorWords SpectralWeightedGraph
  ActualReferenceDDHigherGeometryJets ReferenceWeightedApproximation ReferenceDensityBounds
  CoordinateBootstrapJets PrincipalCommutator ConformalDepth NormalizedPrincipalMetric
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev H0PrincipalEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] H0PrincipalEnergyFunction

theorem exists_nativeH0_principal_commutator_pointwise_energy_bound
    (hF : SphereFischerInner) (g1 g2 : MatrixField)
    (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (L : ℝ) (hL : 0 < L) (K : Set R3) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ 1 → ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ p : ℕ, 1 ≤ p → ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ x ∈ K,
      let beta := actualReferenceBeta g1 L lam δ R p x
      1 ≤ beta →
      coordinateH8 (referenceNormalizedPrincipalDifference g1 g2 L lam) x ≤
        eps * referenceRadius δ R p L x →
      referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ i k : Fin 3, ∀ F : smoothCompactFiniteSphereCore hO hD,
      |⟪(commutator (nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR)
        (nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k *
          coreDirectionalDerivative hO hD (coordinateDirection i) *
          coreDirectionalDerivative hO hD (coordinateDirection k))) F x,F x⟫_ℝ| ≤
        (C * eps) * (beta⁻¹ * ∑ j : Fin 3,
          ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ))
            (coreDirectionalDerivative hO hD (coordinateDirection j) F) x‖^2 +
          beta * ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖^2) := by
  obtain ⟨CP,hCP,hForms⟩ := exists_nativePrincipal_H0_uniform_half_threehalf_forms
    hO hD hF g1 g2 hg1 hg2 L hL K hK
  refine ⟨3*CP,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx beta hb hH8 hsmall i k F
  let H0 := nativeH0 hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR
  let a := nativePrincipalCoefficient hO hD g1 g2 hg1 L lam δ R p hg2 hδ hR i k
  let d (j : Fin 3) := coreDirectionalDerivative hO hD (coordinateDirection j)
  let Z := a*coefficientDerivative (d i) (coefficientDerivative (d k) H0)
  let Ri := a*coefficientDerivative (d k) H0
  let Rk := a*coefficientDerivative (d i) H0
  let b : ℝ := ‖coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x‖
  let f : ℝ := ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖
  let v (j : Fin 3) : ℝ := ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (d j F) x‖
  let E : ℝ := beta⁻¹*(∑ j : Fin 3, (v j)^2)+beta*b^2
  have hbpos : 0 < beta := by linarith
  have hb0 : 0 ≤ beta := hbpos.le
  have hInv : 0 ≤ beta⁻¹ := inv_nonneg.mpr hb0
  have hSum : 0 ≤ ∑ j : Fin 3, (v j)^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hB : beta*b^2 ≤ E := by dsimp only [E]; linarith [mul_nonneg hInv hSum]
  have hE : 0 ≤ E := (mul_nonneg hb0 (sq_nonneg b)).trans hB
  have hvE (j : Fin 3) : beta⁻¹*(v j)^2+beta*b^2 ≤ E := by
    have hs : (v j)^2 ≤ ∑ l : Fin 3, (v l)^2 :=
      Finset.single_le_sum (fun l _ => sq_nonneg _) (Finset.mem_univ j)
    exact add_le_add (mul_le_mul_of_nonneg_left hs hInv) le_rfl
  have hgraph :
      (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x,
        coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x) ∈ sphereBesselGraph hO hD 1 := by
    intro l
    rw [(coreWeightOperator_graph hO hD (besselWeight (3/2 : ℝ)) F x) l,
      (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) F x) l,smul_smul,
      ← SectionFiveErrorForms.besselWeight_add]
    norm_num
  have hi := BoundedAngularShift.inverseDegreeMultiplier_of_besselGraph hO hD _ _ hgraph
  have hf : f ≤ b := by
    change ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) F x‖ ≤ _
    rw [← hi]
    exact ((BoundedAngularShift.inverseDegreeMultiplier hO hD).le_opNorm _).trans
      (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
        (ActualReferenceDDNormalizedCoefficient.norm_inverseDegreeMultiplier_le_one hO hD)
        (norm_nonneg (coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F x))))
  have hZero : |⟪Z F x,F x⟫_ℝ| ≤ (CP*eps)*E := by
    have ht := (hForms lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx
      hb hH8 hsmall i k i k F F).2.2
    change |⟪Z F x,F x⟫_ℝ| ≤ (CP*eps*beta)*f*b at ht
    calc
      _ ≤ (CP*eps*beta)*f*b := ht
      _ ≤ (CP*eps*beta)*b*b := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hf (by positivity)) (norm_nonneg _ : 0 ≤ b)
      _ = (CP*eps)*(beta*b^2) := by ring
      _ ≤ (CP*eps)*E := mul_le_mul_of_nonneg_left hB (mul_nonneg hCP.le heps)
  have hGrad (j l : Fin 3) :
      |⟪(a*coefficientDerivative (d l) H0) (d j F) x,F x⟫_ℝ| ≤ (CP*eps)*E := by
    have ht := (hForms lam hlam δ hδ hδ1 R hR p hp eps heps heps1 x hx
      hb hH8 hsmall i k l l (d j F) F).2.1
    change |⟪(a*coefficientDerivative (d l) H0) (d j F) x,F x⟫_ℝ| ≤ (CP*eps)*(v j)*b at ht
    calc
      _ ≤ (CP*eps)*(v j)*b := ht
      _ = (CP*eps)*((v j)*b) := by ring
      _ ≤ (CP*eps)*(beta⁻¹*(v j)^2+beta*b^2) :=
        mul_le_mul_of_nonneg_left (SectionFiveErrorForms.mul_le_weighted_sq beta (v j) b hbpos)
          (mul_nonneg hCP.le heps)
      _ ≤ (CP*eps)*E := mul_le_mul_of_nonneg_left (hvE j) (mul_nonneg hCP.le heps)
  have hHa : Commute H0 a := by
    dsimp only [H0,a]
    unfold nativePrincipalCoefficient
    exact nativeH0_scalarCentral hO hD hF g1 g2 hg1 L lam δ R p hg2 hδ hR _ _
  have hOp : (commutator H0 (a*d i*d k)) F x =
      -(Z F x)-Ri (d i F) x-Rk (d k F) x := by
    rw [commutator_zero_second (d i) (d k) H0 a hHa]
    rfl
  have htri (z u v : ℝ) : |-z-u-v| ≤ |z|+|u|+|v| := by
    calc
      _ = |-(z+u+v)| := by congr 1; ring
      _ = |z+u+v| := abs_neg _
      _ ≤ |z+u|+|v| := abs_add_le _ _
      _ ≤ |z|+|u|+|v| := add_le_add (abs_add_le _ _) le_rfl
  change |⟪(commutator H0 (a*d i*d k)) F x,F x⟫_ℝ| ≤ ((3*CP)*eps)*E
  rw [hOp,inner_sub_left,inner_sub_left,inner_neg_left]
  calc
    _ ≤ |⟪Z F x,F x⟫_ℝ|+|⟪Ri (d i F) x,F x⟫_ℝ|+|⟪Rk (d k F) x,F x⟫_ℝ| := htri _ _ _
    _ ≤ (CP*eps)*E+(CP*eps)*E+(CP*eps)*E :=
      add_le_add (add_le_add hZero (hGrad i k)) (hGrad k i)
    _ = ((3*CP)*eps)*E := by ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
