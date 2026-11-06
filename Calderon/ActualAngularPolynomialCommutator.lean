import Calderon.HarmonicDerivativeBounds
import Calderon.HarmonicCoordinateCompatibility

set_option autoImplicit false
noncomputable section
open MvPolynomial
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualAngularPolynomialCommutator
open SphereHarmonic SphereDerivativeAdjoint HarmonicCoordinateCompatibility
  HarmonicDerivativeOperator HarmonicDerivativeBounds AngularPolynomial

lemma pderiv_sphereDerivativeAdjoint_commutator (m : ℕ) (i j : Fin 3)
    (q : MvPolynomial (Fin 3) ℝ) :
    pderiv i (sphereDerivativeAdjoint (m+1) j q) -
      sphereDerivativeAdjoint m j (pderiv i q) =
    C (2*(m:ℝ)+5) * (if i=j then q else 0) +
      C (2/(2*(m:ℝ)+3)) * sphereDerivativeAdjoint m j (pderiv i q) -
      C (2*(2*(m:ℝ)+5)/(2*(m:ℝ)+3)^2) * sphereDerivativeAdjoint m i (pderiv j q) := by
  have hd : 2*(m:ℝ)+3 ≠ 0 := by positivity
  have he : 2*(m:ℝ)+1 ≠ 0 := by positivity
  have hk1 : 2*((m+1:ℕ):ℝ)+1 = 2*(m:ℝ)+3 := by push_cast; ring
  have hk3 : 2*((m+1:ℕ):ℝ)+3 = 2*(m:ℝ)+5 := by push_cast; ring
  have h1 : (2/(2*(m:ℝ)+3))*(2*(m:ℝ)+3) = 2 := by field_simp
  have h2 : (2*(2*(m:ℝ)+5)/(2*(m:ℝ)+3)^2)*(2*(m:ℝ)+3) =
      2*(2*(m:ℝ)+5)/(2*(m:ℝ)+3) := by field_simp <;> ring
  have h3 : -(2*(m:ℝ)+5)/(2*(m:ℝ)+3)+(2*(m:ℝ)+3)/(2*(m:ℝ)+1) =
      -2/(2*(m:ℝ)+1)+2*(2*(m:ℝ)+5)/((2*(m:ℝ)+3)*(2*(m:ℝ)+1)) := by
    field_simp <;> ring
  have hpd : pderiv i (pderiv j q) = pderiv j (pderiv i q) :=
    pderiv_pderiv_comm i j q
  have hX : pderiv i (X j : MvPolynomial (Fin 3) ℝ) = if i=j then 1 else 0 := by
    by_cases hij : i=j
    · subst j
      simp
    · simp [hij,pderiv_X_of_ne (Ne.symm hij)]
  simp only [div_eq_mul_inv,← inv_pow,mul_inv_rev] at h1 h2 h3
  have h1C := congrArg (C : ℝ →+* MvPolynomial (Fin 3) ℝ) h1
  have h2C := congrArg (C : ℝ →+* MvPolynomial (Fin 3) ℝ) h2
  have h3C := congrArg (C : ℝ →+* MvPolynomial (Fin 3) ℝ) h3
  simp only [map_add,map_sub,map_mul,map_neg,map_ofNat,map_pow,pow_two] at h1C h2C h3C
  simp only [sphereDerivativeAdjoint,coordinateHarmonicRaising,hk1,hk3,
    pderiv_C_mul,map_sub,pderiv_mul,pderiv_C,hX,pderiv_radiusSq,← hpd]
  simp only [div_eq_mul_inv,← inv_pow,mul_inv_rev]
  by_cases hij : i=j
  · subst j
    simp only [eq_self,ite_true,if_pos rfl,zero_mul,zero_add,add_zero,one_mul,mul_one,pow_two,
      map_add,map_sub,map_mul,map_neg,map_ofNat,map_pow]
    linear_combination
      -(X i*pderiv i q - C ((2*(m:ℝ)+1)⁻¹)*radiusSq*pderiv i (pderiv i q))*h1C +
      (X i*pderiv i q - C ((2*(m:ℝ)+1)⁻¹)*radiusSq*pderiv i (pderiv i q))*h2C +
      (radiusSq*pderiv i (pderiv i q))*h3C
  · have hji : j≠i := Ne.symm hij
    simp only [ite_false,if_neg hij,zero_mul,zero_add,add_zero,mul_zero,one_mul,mul_one,pow_two,
      map_add,map_sub,map_mul,map_neg,map_ofNat,map_pow]
    linear_combination
      -(X j*pderiv i q - C ((2*(m:ℝ)+1)⁻¹)*radiusSq*pderiv i (pderiv j q))*h1C +
      (X i*pderiv j q - C ((2*(m:ℝ)+1)⁻¹)*radiusSq*pderiv i (pderiv j q))*h2C +
      (radiusSq*pderiv i (pderiv j q))*h3C

lemma pderiv_sphereDerivativeAdjoint_zero (i j : Fin 3) (c : ℝ) :
    pderiv i (sphereDerivativeAdjoint 0 j (C c)) = if i=j then C (3*c) else 0 := by
  rw [sphereDerivativeAdjoint_zero_C]
  by_cases h : i=j
  · subst j
    simp [pderiv_mul,pderiv_X]
  · simp [pderiv_mul,pderiv_X,h,Ne.symm h]

lemma harmonicDerivative_apply_polynomial (hF : SphereFischerInner) (m : ℕ)
    (i : Fin 3) (q : MvPolynomial (Fin 3) ℝ) (hq : q ∈ harmonicHomogeneous (m+1)) :
    (harmonicDerivative hF m i
      ⟨polynomialSphereL2 q,polynomialSphereL2_mem (m+1) q hq⟩ : SphereL2) =
      polynomialSphereL2 (pderiv i q) := by
  exact congrArg Subtype.val (harmonicDerivative_apply_image hF m i ⟨q,hq⟩)

lemma harmonicDerivativeAdjoint_apply_polynomial (hF : SphereFischerInner) (m : ℕ)
    (i : Fin 3) (q : MvPolynomial (Fin 3) ℝ) (hq : q ∈ harmonicHomogeneous m) :
    (harmonicDerivativeAdjoint hF m i
      ⟨polynomialSphereL2 q,polynomialSphereL2_mem m q hq⟩ : SphereL2) =
      polynomialSphereL2 (sphereDerivativeAdjoint m i q) := by
  exact congrArg Subtype.val (harmonicDerivativeAdjoint_apply_image hF m i ⟨q,hq⟩)

theorem harmonicDerivativeAdjoint_commutator (hF : SphereFischerInner) (m : ℕ)
    (i j : Fin 3) (u : harmonicSphereSubspace (m+1)) :
    harmonicDerivative hF (m+1) i (harmonicDerivativeAdjoint hF (m+1) j u) -
      harmonicDerivativeAdjoint hF m j (harmonicDerivative hF m i u) =
    (2*(m:ℝ)+5) • (if i=j then u else 0) +
      (2/(2*(m:ℝ)+3)) • harmonicDerivativeAdjoint hF m j (harmonicDerivative hF m i u) -
      (2*(2*(m:ℝ)+5)/(2*(m:ℝ)+3)^2) • harmonicDerivativeAdjoint hF m i (harmonicDerivative hF m j u) := by
  obtain ⟨q,rfl⟩ := SmoothSphereRotationProjection.harmonicPolynomialSphereMap_surjective (m+1) u
  let qr : harmonicHomogeneous ((m+1)+1) :=
    ⟨sphereDerivativeAdjoint (m+1) j (q : MvPolynomial (Fin 3) ℝ),
      sphereDerivativeAdjoint_harmonicHomogeneous (m+1) j q q.property⟩
  let qi : harmonicHomogeneous m :=
    ⟨pderiv i (q : MvPolynomial (Fin 3) ℝ),pderiv_harmonicHomogeneous_succ m i q q.property⟩
  let qj : harmonicHomogeneous m :=
    ⟨pderiv j (q : MvPolynomial (Fin 3) ℝ),pderiv_harmonicHomogeneous_succ m j q q.property⟩
  have hr : harmonicDerivativeAdjoint hF (m+1) j (SmoothSphereRotationProjection.harmonicPolynomialSphereMap (m+1) q) =
      SmoothSphereRotationProjection.harmonicPolynomialSphereMap ((m+1)+1) qr := harmonicDerivativeAdjoint_apply_image hF (m+1) j q
  have hi : harmonicDerivative hF m i (SmoothSphereRotationProjection.harmonicPolynomialSphereMap (m+1) q) =
      SmoothSphereRotationProjection.harmonicPolynomialSphereMap m qi := harmonicDerivative_apply_image hF m i q
  have hj : harmonicDerivative hF m j (SmoothSphereRotationProjection.harmonicPolynomialSphereMap (m+1) q) =
      SmoothSphereRotationProjection.harmonicPolynomialSphereMap m qj := harmonicDerivative_apply_image hF m j q
  rw [hr,hi,hj,harmonicDerivative_apply_image,harmonicDerivativeAdjoint_apply_image,
    harmonicDerivativeAdjoint_apply_image]
  apply Subtype.ext
  simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul,
    apply_ite, Submodule.coe_zero]
  dsimp only [harmonicPolynomialDerivativeMap, harmonicPolynomialDerivativeAdjointMap,
    SmoothSphereRotationProjection.harmonicPolynomialSphereMap, qr, qi, qj]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk]
  have hp := congrArg polynomialSphereL2 (pderiv_sphereDerivativeAdjoint_commutator m i j q)
  simp only [← smul_eq_C_mul] at hp
  by_cases hij : i=j
  · simpa only [map_sub,map_add,map_smul,apply_ite,map_zero,if_pos hij,smul_zero] using hp
  · simpa only [map_sub,map_add,map_smul,apply_ite,map_zero,if_neg hij,smul_zero] using hp

theorem harmonicDerivativeAdjoint_zero_commutator (hF : SphereFischerInner)
    (i j : Fin 3) (u : harmonicSphereSubspace 0) :
    harmonicDerivative hF 0 i (harmonicDerivativeAdjoint hF 0 j u) =
      if i=j then (3:ℝ) • u else 0 := by
  obtain ⟨q,rfl⟩ := SmoothSphereRotationProjection.harmonicPolynomialSphereMap_surjective 0 u
  let qr : harmonicHomogeneous (0+1) :=
    ⟨sphereDerivativeAdjoint 0 j (q : MvPolynomial (Fin 3) ℝ),
      sphereDerivativeAdjoint_harmonicHomogeneous 0 j q q.property⟩
  have hr : harmonicDerivativeAdjoint hF 0 j (SmoothSphereRotationProjection.harmonicPolynomialSphereMap 0 q) =
      SmoothSphereRotationProjection.harmonicPolynomialSphereMap (0+1) qr := harmonicDerivativeAdjoint_apply_image hF 0 j q
  rw [hr,harmonicDerivative_apply_image]
  apply Subtype.ext
  simp only [apply_ite, Submodule.coe_smul, Submodule.coe_zero]
  dsimp only [harmonicPolynomialDerivativeMap,
    SmoothSphereRotationProjection.harmonicPolynomialSphereMap, qr]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk]
  have hq := eq_C_of_harmonicHomogeneous_zero q q.property
  rw [hq]
  have hp := congrArg polynomialSphereL2
    (pderiv_sphereDerivativeAdjoint_zero i j ((q : MvPolynomial (Fin 3) ℝ).coeff 0))
  have he : (C (3*(q : MvPolynomial (Fin 3) ℝ).coeff 0) : MvPolynomial (Fin 3) ℝ) =
      (3:ℝ) • C ((q : MvPolynomial (Fin 3) ℝ).coeff 0) := by simp [smul_eq_C_mul,map_mul]
  rw [he] at hp
  by_cases hij : i=j
  · simpa only [apply_ite,map_zero,map_smul,if_pos hij] using hp
  · simpa only [apply_ite,map_zero,map_smul,if_neg hij] using hp

end OAI.AnisotropicCalderon.ActualAngularPolynomialCommutator
