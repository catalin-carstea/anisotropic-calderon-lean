import Calderon.FixedDirichletRegularity
import Calderon.FixedSobolevCalculus
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import TauCeti.Analysis.Sobolev.TestFunctionLp
import TauCeti.Analysis.Sobolev.Wkp.SecondOrder
import TauCeti.Analysis.PDE.EnergyForm.Sobolev
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Sobolev.Leibniz

/-! Differentiating a weak equation along a smooth divergence-free vector field
(helper for task 05). -/

noncomputable section
open MeasureTheory TopologicalSpace
open scoped InnerProductSpace ContDiff Distributions Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity.DiffEq
open TauCeti TauCeti.PDE EnergyBridge

/-- The `i`th standard basis vector. -/
def e (i : Fin 3) : R3 := EuclideanSpace.single i (1 : ℝ)

lemma coord_eq_inner (y : R3) (i : Fin 3) : y i = ⟪y, e i⟫_ℝ := by
  simp [e, EuclideanSpace.inner_single_right]

/-- Partial derivative along `e i`. -/
def pd (g : R3 → ℝ) (i : Fin 3) : R3 → ℝ := fun x => fderiv ℝ g x (e i)

/-- `g` is (the coercion of) a test function on the ball. -/
def TF (g : R3 → ℝ) : Prop := ∃ ψ : 𝓓(ballOpens, ℝ), (ψ : R3 → ℝ) = g

end OAI.AnisotropicCalderon.Regularity.DiffEq

namespace OAI.AnisotropicCalderon.Regularity.DiffEq.TF
open TauCeti TauCeti.PDE EnergyBridge

lemma of (ψ : 𝓓(ballOpens, ℝ)) : TF ψ := ⟨ψ, rfl⟩

lemma contDiff {g : R3 → ℝ} (h : TF g) : ContDiff ℝ ∞ g := by
  obtain ⟨ψ, rfl⟩ := h; exact ψ.contDiff

lemma differentiableAt {g : R3 → ℝ} (h : TF g) (x : R3) : DifferentiableAt ℝ g x :=
  (h.contDiff.differentiable (by simp)) x

lemma zero_of_notMem {g : R3 → ℝ} (h : TF g) {x : R3} (hx : x ∉ (ballOpens : Set R3)) :
    g x = 0 := by
  obtain ⟨ψ, rfl⟩ := h
  exact image_eq_zero_of_notMem_tsupport (fun hmem => hx (ψ.tsupport_subset hmem))

lemma mul {g : R3 → ℝ} (h : TF g) {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) :
    TF (fun x => g x * f x) := by
  obtain ⟨ψ, rfl⟩ := h
  exact ⟨⟨(ψ : R3 → ℝ) * f, ψ.contDiff.mul hf, ψ.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans ψ.tsupport_subset⟩, rfl⟩

lemma add {g h : R3 → ℝ} (hg : TF g) (hh : TF h) : TF (fun x => g x + h x) := by
  obtain ⟨ψ, rfl⟩ := hg; obtain ⟨χ, rfl⟩ := hh
  exact ⟨ψ + χ, rfl⟩

lemma zero : TF (fun _ => 0) := ⟨0, rfl⟩

lemma sum {ι : Type*} (s : Finset ι) {g : ι → R3 → ℝ} (h : ∀ i, TF (g i)) :
    TF (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using TF.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

lemma deriv {g : R3 → ℝ} (h : TF g) (i : Fin 3) : TF (pd g i) := by
  obtain ⟨ψ, rfl⟩ := h
  refine ⟨TestFunction.lineDerivCLM ℝ (e i) ψ, ?_⟩
  funext x
  rw [TestFunction.lineDerivCLM_apply_of_le le_top]
  exact ((ψ.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv

lemma integrable {g : R3 → ℝ} (h : TF g) {w : R3 → ℝ}
    (hw : LocallyIntegrableOn w (ballOpens : Set R3) volume) :
    Integrable (fun x => g x * w x) volume := by
  obtain ⟨ψ, rfl⟩ := h
  simpa [smul_eq_mul] using integrable_smul_of_locallyIntegrableOn hw ψ

/-- Integration by parts against a weak derivative, as a vanishing integral. -/
lemma null {g : R3 → ℝ} (h : TF g) {u u' : R3 → ℝ} {i : Fin 3}
    (hu : HasWeakLineDerivOn volume ballOpens u u' (e i)) :
    Integrable (fun x => pd g i x * u x + g x * u' x) volume ∧
      ∫ x, (pd g i x * u x + g x * u' x) = 0 := by
  have h1 := (h.deriv i).integrable hu.locallyIntegrableOn
  have h2 := h.integrable hu.locallyIntegrableOn_deriv
  refine ⟨h1.add h2, ?_⟩
  rw [integral_add h1 h2]
  obtain ⟨ψ, rfl⟩ := h
  have := hu.integral_lineDeriv_smul_eq_neg_integral_smul ψ
  simp only [smul_eq_mul] at this
  have e1 : (fun x => lineDeriv ℝ (ψ : R3 → ℝ) x (e i) * u x) = fun x => pd ψ i x * u x := by
    funext x
    rw [((ψ.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv]; rfl
  rw [e1] at this
  rw [this]; ring

end OAI.AnisotropicCalderon.Regularity.DiffEq.TF

namespace OAI.AnisotropicCalderon.Regularity.DiffEq
open TauCeti TauCeti.PDE EnergyBridge

lemma pd_pd_comm {g : R3 → ℝ} (hg : ContDiff ℝ ∞ g) (i l : Fin 3) (x : R3) :
    pd (pd g i) l x = pd (pd g l) i x := by
  have hdf : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := ∞) le_rfl).differentiable (by simp)
  have key : ∀ u u' : R3, fderiv ℝ (fun y => fderiv ℝ g y u) x u' =
      fderiv ℝ (fderiv ℝ g) x u' u := by
    intro u u'
    rw [fderiv_clm_apply (hdf x) (differentiableAt_const u)]
    simp
  show fderiv ℝ (fun y => fderiv ℝ g y (e i)) x (e l) = fderiv ℝ (fun y => fderiv ℝ g y (e l)) x (e i)
  rw [key, key]
  exact ((hg.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)) (e l) (e i)

lemma pd_mul {x : R3} {f g : R3 → ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (i : Fin 3) : pd (fun y => f y * g y) i x = pd f i x * g x + f x * pd g i x := by
  simp only [pd]
  rw [fderiv_fun_mul hf hg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma pd_sum {x : R3} {ι : Type*} (s : Finset ι) {f : ι → R3 → ℝ}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) (i : Fin 3) :
    pd (fun y => ∑ j ∈ s, f j y) i x = ∑ j ∈ s, pd (f j) i x := by
  simp only [pd]
  rw [fderiv_fun_sum fun j _ => hf j]
  simp

lemma pd_coord {x : R3} {c : R3 → R3} (hc : DifferentiableAt ℝ c x) (l i : Fin 3) :
    pd (fun y => c y l) i x = fderiv ℝ c x (e i) l := by
  simp only [pd]
  have h := ((EuclideanSpace.proj l : R3 →L[ℝ] ℝ).hasFDerivAt.comp x hc.hasFDerivAt).fderiv
  have h2 : (fun y => c y l) = (EuclideanSpace.proj l : R3 →L[ℝ] ℝ) ∘ c := rfl
  rw [h2, h]
  rfl

lemma alg (φ0 f0 P0 : ℝ) (p : Fin 3 → ℝ) (q : Fin 3 → Fin 3 → ℝ) (A : Fin 3 → Fin 3 → ℝ)
    (dA : Fin 3 → Fin 3 → Fin 3 → ℝ) (c : Fin 3 → ℝ) (dc : Fin 3 → Fin 3 → ℝ) (G : Fin 3 → ℝ)
    (Dm : Fin 3 → Fin 3 → ℝ) (gF : Fin 3 → ℝ) (dψ : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (dP : Fin 3 → ℝ) (dφc : Fin 3 → ℝ)
    (hψ : ∀ i k l, dψ i k l = dA i k l * c l + A i k * dc l l)
    (hP : ∀ i, dP i = ∑ l, (q i l * c l + p l * dc l i))
    (hφc : ∀ l, dφc l = p l * c l + φ0 * dc l l)
    (hP0 : P0 = ∑ l, p l * c l)
    (hdiv : ∑ l, dc l l = 0) :
    ∑ i, ∑ k, p i * (A i k * ∑ l, (c l * Dm l k + G l * dc l k)) =
      (∑ l, c l * gF l) * φ0 +
        ∑ i, ∑ k, p i * ((∑ m, A i m * dc k m - ∑ l, c l * dA i k l + ∑ j, A j k * dc i j) * G k) +
        ((∑ i, ∑ k, ∑ l, (q i l * ((A i k * c l) • G k) +
            p i * ((A i k * c l) • Dm l k + dψ i k l • G k))) -
          (∑ i, ∑ k, (dP i * A i k) * G k - P0 * f0) -
          ∑ l, (dφc l * f0 + (φ0 * c l) * gF l)) := by
  simp only [hψ, hP, hφc, hP0, smul_eq_mul]
  have key := congrArg (fun t => (φ0 * f0 - ∑ i, ∑ k, p i * A i k * G k) * t) hdiv
  simp only [Fin.sum_univ_three] at key ⊢
  linear_combination key

/-- Integrable with vanishing integral. -/
def Null (Z : R3 → ℝ) : Prop := Integrable Z volume ∧ ∫ x, Z x = 0

end OAI.AnisotropicCalderon.Regularity.DiffEq

namespace OAI.AnisotropicCalderon.Regularity.DiffEq.Null
open TauCeti TauCeti.PDE EnergyBridge

lemma sub {Z₁ Z₂ : R3 → ℝ} (h₁ : Null Z₁) (h₂ : Null Z₂) : Null (fun x => Z₁ x - Z₂ x) :=
  ⟨h₁.1.sub h₂.1, by rw [integral_sub h₁.1 h₂.1, h₁.2, h₂.2, sub_zero]⟩

lemma sum {ι : Type*} (s : Finset ι) {Z : ι → R3 → ℝ} (h : ∀ i, Null (Z i)) :
    Null (fun x => ∑ i ∈ s, Z i x) :=
  ⟨integrable_finsetSum s fun i _ => (h i).1, by
    rw [integral_finsetSum s fun i _ => (h i).1]
    exact Finset.sum_eq_zero fun i _ => (h i).2⟩

end OAI.AnisotropicCalderon.Regularity.DiffEq.Null

namespace OAI.AnisotropicCalderon.Regularity.DiffEq
open TauCeti TauCeti.PDE EnergyBridge

lemma contDiff_entry {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a) (i k : Fin 3) :
    ContDiff ℝ ∞ (fun x => a x i k) :=
  contDiff_pi.1 (contDiff_pi.1 ha i) k

lemma contDiff_coord {c : R3 → R3} (hc : ContDiff ℝ ∞ c) (l : Fin 3) :
    ContDiff ℝ ∞ (fun x => c x l) :=
  (EuclideanSpace.proj l : R3 →L[ℝ] ℝ).contDiff.comp hc

lemma matrixBilinearForm_eq_sum (A : Matrix (Fin 3) (Fin 3) ℝ) (η ξ : R3) :
    matrixBilinearForm A η ξ = ∑ i, ∑ k, η i * (A i k * ξ k) := by
  rw [matrixBilinearForm_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]

lemma gradient_coord (g : R3 → ℝ) (x : R3) (i : Fin 3) :
    gradient g x i = pd g i x := by
  rw [coord_eq_inner, inner_gradient_left]; rfl

/-- Pass to a set integral over the ball. -/
lemma integral_eq_setIntegral {Z : R3 → ℝ} (hZ : ∀ x ∉ (ballOpens : Set R3), Z x = 0) :
    ∫ x, Z x = ∫ x in (ballOpens : Set R3), Z x :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hZ).symm

lemma coordDeriv {u : R3 → ℝ} {G : R3 → R3}
    (hu : HasWeakFDerivOn volume ballOpens u (fun x => innerSL ℝ (G x))) (k : Fin 3) :
    HasWeakLineDerivOn volume ballOpens u (fun x => G x k) (e k) :=
  (hu.hasWeakLineDerivOn (e k)).congr_ae_deriv
    (Filter.Eventually.of_forall fun x => by simp [coord_eq_inner])

lemma vecDeriv {G : R3 → R3} {D : R3 → R3 →L[ℝ] R3}
    (hG : HasWeakFDerivOn volume ballOpens G D) (k l : Fin 3) :
    HasWeakLineDerivOn volume ballOpens (fun x => G x k) (fun x => D x (e l) k) (e l) :=
  (hG.hasWeakLineDerivOn (e l)).clm_comp (EuclideanSpace.proj k : R3 →L[ℝ] ℝ)

end OAI.AnisotropicCalderon.Regularity.DiffEq

namespace OAI.AnisotropicCalderon.Regularity.DiffEq.TF
open TauCeti TauCeti.PDE EnergyBridge

lemma ibp {g : R3 → ℝ} (h : TF g) {u u' : R3 → ℝ} {i : Fin 3}
    (hu : HasWeakLineDerivOn volume ballOpens u u' (e i)) :
    ∫ x, g x * u' x = -∫ x, pd g i x * u x := by
  have h1 := (h.deriv i).integrable hu.locallyIntegrableOn
  have h2 := h.integrable hu.locallyIntegrableOn_deriv
  have := (h.null hu).2
  rw [integral_add h1 h2] at this
  linarith

end OAI.AnisotropicCalderon.Regularity.DiffEq.TF

namespace OAI.AnisotropicCalderon.Regularity.DiffEq
open TauCeti TauCeti.PDE EnergyBridge

lemma lineDeriv_eq_pd (ψ : 𝓓(ballOpens, ℝ)) (x : R3) (i : Fin 3) :
    lineDeriv ℝ (ψ : R3 → ℝ) x (e i) = pd ψ i x :=
  ((ψ.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv

/-- Symmetry of weak second derivatives: `∂ₗ Gₖ = ∂ₖ Gₗ`. -/
lemma symmDeriv {u : R3 → ℝ} {G : R3 → R3} {D : R3 → R3 →L[ℝ] R3}
    (hu : HasWeakFDerivOn volume ballOpens u (fun x => innerSL ℝ (G x)))
    (hG : HasWeakFDerivOn volume ballOpens G D) (k l : Fin 3) :
    HasWeakLineDerivOn volume ballOpens (fun x => G x k) (fun x => D x (e k) l) (e l) := by
  have h1 := vecDeriv hG l k
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨inferInstance, (coordDeriv hu k).locallyIntegrableOn_deriv,
    h1.locallyIntegrableOn_deriv, fun ψ => ?_⟩
  rw [← h1.integral_lineDeriv_smul_eq_neg_integral_smul ψ]
  simp only [smul_eq_mul, lineDeriv_eq_pd]
  rw [((TF.of ψ).deriv l).ibp (coordDeriv hu k), ((TF.of ψ).deriv k).ibp (coordDeriv hu l)]
  simp only [pd_pd_comm ψ.contDiff l k]

/-- The correction matrix. -/
def Mf (a : R3 → Matrix (Fin 3) (Fin 3) ℝ) (c : R3 → R3) : R3 → Matrix (Fin 3) (Fin 3) ℝ :=
  fun x i k => ∑ m, a x i m * pd (fun y => c y k) m x - ∑ l, c x l * pd (fun y => a y i k) l x +
    ∑ j, a x j k * pd (fun y => c y i) j x

lemma contDiff_pd {g : R3 → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin 3) : ContDiff ℝ ∞ (pd g i) :=
  (hg.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

lemma contDiff_Mf {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    {c : R3 → R3} (hc : ContDiff ℝ ∞ c) (i k : Fin 3) : ContDiff ℝ ∞ (fun x => Mf a c x i k) := by
  simp only [Mf]
  have hA := contDiff_entry ha
  have hC := contDiff_coord hc
  refine ((ContDiff.sum fun m _ => (hA i m).mul (contDiff_pd (hC k) m)).sub
    (ContDiff.sum fun l _ => (hC l).mul (contDiff_pd (hA i k) l))).add
    (ContDiff.sum fun j _ => (hA j k).mul (contDiff_pd (hC i) j))

lemma core {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    {c : R3 → R3} (hc : ContDiff ℝ ∞ c)
    (hdiv : ∀ x, ∑ l, pd (fun y => c y l) l x = 0)
    {u : R3 → ℝ} {G : R3 → R3} {D : R3 → R3 →L[ℝ] R3} {f : R3 → ℝ} {gF : R3 → R3}
    (hu : HasWeakFDerivOn volume ballOpens u (fun x => innerSL ℝ (G x)))
    (hG : HasWeakFDerivOn volume ballOpens G D)
    (hF : HasWeakFDerivOn volume ballOpens f (fun x => innerSL ℝ (gF x)))
    (heq : ∀ φ : 𝓓(ballOpens, ℝ),
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x) (G x) =
        ∫ x in (ballOpens : Set R3), f x * φ x)
    (φ : 𝓓(ballOpens, ℝ)) :
    ∫ x, ∑ i, ∑ k, pd φ i x * (a x i k *
        ∑ l, (c x l * D x (e k) l + G x l * pd (fun y => c y l) k x)) =
      (∫ x, (∑ l, c x l * gF x l) * φ x) + ∫ x, ∑ i, ∑ k, pd φ i x * (Mf a c x i k * G x k) := by
  have hA := contDiff_entry ha
  have hC := contDiff_coord hc
  have hφ := TF.of φ
  have hGl : ∀ k, LocallyIntegrableOn (fun x => G x k) (ballOpens : Set R3) volume :=
    fun k => (coordDeriv hu k).locallyIntegrableOn_deriv
  have hgFl : ∀ l, LocallyIntegrableOn (fun x => gF x l) (ballOpens : Set R3) volume :=
    fun l => (coordDeriv hF l).locallyIntegrableOn_deriv
  have hfl : LocallyIntegrableOn f (ballOpens : Set R3) volume :=
    (coordDeriv hF 0).locallyIntegrableOn
  -- the three families of vanishing integrals
  have Z1 : ∀ i k l, Null (fun x => pd (pd φ i) l x * ((a x i k * c x l) • G x k) +
      pd φ i x * ((a x i k * c x l) • D x (e k) l +
        pd (fun y => a y i k * c y l) l x • G x k)) := fun i k l =>
    (hφ.deriv i).null (HasWeakLineDerivOn.contDiff_smul (symmDeriv hu hG k l) ((hA i k).mul (hC l)))
  have hPφ : TF (fun y => ∑ l, pd φ l y * c y l) :=
    TF.sum _ fun l => (hφ.deriv l).mul (hC l)
  have Z2 : Null (fun x => ∑ i, ∑ k, (pd (fun y => ∑ l, pd φ l y * c y l) i x * a x i k) * G x k -
      (∑ l, pd φ l x * c x l) * f x) := by
    obtain ⟨ψP, hψP⟩ := id hPφ
    have i1 : Integrable (fun x => ∑ i, ∑ k,
        (pd (fun y => ∑ l, pd φ l y * c y l) i x * a x i k) * G x k) volume :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
        ((hPφ.deriv i).mul (hA i k)).integrable (hGl k)
    have i2 := hPφ.integrable hfl
    refine ⟨i1.sub i2, ?_⟩
    rw [integral_sub i1 i2, sub_eq_zero]
    have h := heq ψP
    rw [hψP] at h
    calc ∫ x, ∑ i, ∑ k, (pd (fun y => ∑ l, pd φ l y * c y l) i x * a x i k) * G x k
        = ∫ x in (ballOpens : Set R3), ∑ i, ∑ k,
            (pd (fun y => ∑ l, pd φ l y * c y l) i x * a x i k) * G x k :=
          integral_eq_setIntegral (fun x hx => by simp [(hPφ.deriv _).zero_of_notMem hx])
      _ = ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x)
            (gradient (fun y => ∑ l, pd φ l y * c y l) x) (G x) := by
          refine setIntegral_congr_fun ballOpens.isOpen.measurableSet fun x _ => ?_
          simp only [matrixBilinearForm_eq_sum, gradient_coord]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => mul_assoc _ _ _
      _ = ∫ x in (ballOpens : Set R3), f x * ∑ l, pd φ l x * c x l := h
      _ = ∫ x, (∑ l, pd φ l x * c x l) * f x := by
          rw [integral_eq_setIntegral (fun x hx => by simp [hPφ.zero_of_notMem hx])]
          exact setIntegral_congr_fun ballOpens.isOpen.measurableSet fun x _ => mul_comm _ _
  have Z3 : ∀ l, Null (fun x => pd (fun y => φ y * c y l) l x * f x + (φ x * c x l) * gF x l) :=
    fun l => (hφ.mul (hC l)).null (coordDeriv hF l)
  have hZ := ((Null.sum Finset.univ fun i => Null.sum Finset.univ fun k =>
    Null.sum Finset.univ fun l => Z1 i k l).sub Z2).sub (Null.sum Finset.univ Z3)
  have hR1 : Integrable (fun x => (∑ l, c x l * gF x l) * φ x) volume := by
    refine (integrable_finsetSum Finset.univ fun l _ => (hφ.mul (hC l)).integrable (hgFl l)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hR2 : Integrable (fun x => ∑ i, ∑ k, pd φ i x * (Mf a c x i k * G x k)) volume := by
    refine (integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ
      fun k _ => ((hφ.deriv i).mul (contDiff_Mf ha hc i k)).integrable (hGl k)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hpt : ∀ x, ∑ i, ∑ k, pd φ i x * (a x i k *
        ∑ l, (c x l * D x (e k) l + G x l * pd (fun y => c y l) k x)) =
      (∑ l, c x l * gF x l) * φ x + ∑ i, ∑ k, pd φ i x * (Mf a c x i k * G x k) +
        (((∑ i, ∑ k, ∑ l, (pd (pd φ i) l x * ((a x i k * c x l) • G x k) +
          pd φ i x * ((a x i k * c x l) • D x (e k) l +
            pd (fun y => a y i k * c y l) l x • G x k))) -
          (∑ i, ∑ k, (pd (fun y => ∑ l, pd φ l y * c y l) i x * a x i k) * G x k -
            (∑ l, pd φ l x * c x l) * f x)) -
          ∑ l, (pd (fun y => φ y * c y l) l x * f x + (φ x * c x l) * gF x l)) := by
    intro x
    have dA : ∀ i k, DifferentiableAt ℝ (fun y => a y i k) x :=
      fun i k => ((hA i k).differentiable (by simp)) x
    have dC : ∀ l, DifferentiableAt ℝ (fun y => c y l) x :=
      fun l => ((hC l).differentiable (by simp)) x
    have dφ : ∀ l, DifferentiableAt ℝ (pd φ l) x := fun l => (hφ.deriv l).differentiableAt x
    exact alg (φ x) (f x) (∑ l, pd φ l x * c x l) (fun i => pd φ i x)
      (fun i l => pd (pd φ i) l x) (fun i k => a x i k) (fun i k l => pd (fun y => a y i k) l x)
      (fun l => c x l) (fun l m => pd (fun y => c y l) m x) (fun k => G x k)
      (fun l k => D x (e k) l) (fun l => gF x l) (fun i k l => pd (fun y => a y i k * c y l) l x)
      (fun i => pd (fun y => ∑ l, pd φ l y * c y l) i x)
      (fun l => pd (fun y => φ y * c y l) l x)
      (fun i k l => pd_mul (dA i k) (dC l) l)
      (fun i => by
        rw [pd_sum (f := fun l y => pd φ l y * c y l) _ (fun l => (dφ l).mul (dC l))]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [pd_mul (dφ l) (dC l), pd_pd_comm φ.contDiff l i])
      (fun l => pd_mul (hφ.differentiableAt x) (dC l) l) rfl (hdiv x)
  have hR12 : Integrable (fun x => (∑ l, c x l * gF x l) * φ x +
      ∑ i, ∑ k, pd φ i x * (Mf a c x i k * G x k)) volume := hR1.add hR2
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hR12 hZ.1,
    hZ.2, add_zero, integral_add hR1 hR2]

lemma sum_smul_e_apply (g : Fin 3 → ℝ) (k : Fin 3) : (∑ k', g k' • e k') k = g k := by
  simp [e, Pi.single_apply]

lemma memLp_mul_cont {h : R3 → ℝ} (hh : Continuous h) {w : R3 → ℝ}
    (hw : MemLp w 2 ((volume : Measure R3).restrict ballOpens)) :
    MemLp (fun x => h x * w x) 2 ((volume : Measure R3).restrict ballOpens) := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : R3) 1).exists_bound_of_continuousOn
    hh.continuousOn
  refine hw.of_le_mul (c := K) (hh.aestronglyMeasurable.mul hw.aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem ballOpens.isOpen.measurableSet fun x hx => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hK x (Metric.ball_subset_closedBall hx)) (norm_nonneg _)

lemma main_abstract {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    {c : R3 → R3} (hc : ContDiff ℝ ∞ c)
    (hdiv : ∀ x, ∑ l : Fin 3, fderiv ℝ c x (EuclideanSpace.single l 1) l = 0)
    (v : W1p (volume : Measure R3) ballOpens 2) {D : R3 → R3 →L[ℝ] R3}
    (hDL : ∀ k l, MemLp (fun x => D x (e k) l) 2 ((volume : Measure R3).restrict ballOpens))
    (hG : HasWeakFDerivOn volume ballOpens (W1p.gradient v) D)
    (Fw : W1p (volume : Measure R3) ballOpens 2)
    (heq : ∀ φ : 𝓓(ballOpens, ℝ),
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x)
          (W1p.gradient v x) =
        ∫ x in (ballOpens : Set R3), W1p.value Fw x * φ x) :
    ∃ w : W1p (volume : Measure R3) ballOpens 2,
      (⇑(W1p.value w) =ᵐ[(volume : Measure R3).restrict ballOpens]
        fun x => ⟪c x, W1p.gradient v x⟫_ℝ) ∧
      ∃ M : R3 → Matrix (Fin 3) (Fin 3) ℝ, ContDiff ℝ ∞ M ∧
        ∀ φ : 𝓓(ballOpens, ℝ),
          ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x)
              (W1p.gradient w x) =
            (∫ x in (ballOpens : Set R3), ⟪c x, W1p.gradient Fw x⟫_ℝ * φ x) +
              ∫ x in (ballOpens : Set R3), matrixBilinearForm (M x) (gradient (φ : R3 → ℝ) x)
                (W1p.gradient v x) := by
  have hC := contDiff_coord hc
  have hu := W1p.hasWeakFDerivOn v
  have hF := W1p.hasWeakFDerivOn Fw
  have hdiv' : ∀ x, ∑ l, pd (fun y => c y l) l x = 0 := fun x => by
    rw [← hdiv x]
    exact Finset.sum_congr rfl fun l _ => pd_coord ((hc.differentiable (by simp)) x) l l
  have hGL : ∀ l, MemLp (fun x => W1p.gradient v x l) 2
      ((volume : Measure R3).restrict ballOpens) := fun l =>
    (EuclideanSpace.proj l : R3 →L[ℝ] ℝ).comp_memLp' (Lp.memLp _)
  have hval : MemLp (fun x => ∑ l, c x l * W1p.gradient v x l) 2
      ((volume : Measure R3).restrict ballOpens) :=
    memLp_finsetSum _ fun l _ => memLp_mul_cont (hC l).continuous (hGL l)
  have hgk : ∀ k, MemLp (fun x => ∑ l, (c x l * D x (e k) l +
      W1p.gradient v x l * pd (fun y => c y l) k x)) 2 ((volume : Measure R3).restrict ballOpens) :=
    fun k => memLp_finsetSum _ fun l _ => (memLp_mul_cont (hC l).continuous (hDL k l)).add
      (by simpa only [mul_comm] using memLp_mul_cont (contDiff_pd (hC l) k).continuous (hGL l))
  have hgrad : MemLp (fun x => ∑ k, (∑ l, (c x l * D x (e k) l +
      W1p.gradient v x l * pd (fun y => c y l) k x)) • e k) 2
      ((volume : Measure R3).restrict ballOpens) :=
    memLp_finsetSum _ fun k _ =>
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (e k)).comp_memLp' (hgk k)).ae_eq
        (Filter.Eventually.of_forall fun x => by simp [Finset.sum_smul])
  have hw : HasWeakFDerivOn volume ballOpens (⇑(hval.toLp _))
      (fun x => innerSL ℝ ((hgrad.toLp _) x)) := by
    refine (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.hasWeakFDerivOn_of_forall
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((Lp.memLp _).locallyIntegrable (by norm_num))) fun k => ?_
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    have S := HasWeakLineDerivOn.sum Finset.univ
      (fun l _ => HasWeakLineDerivOn.contDiff_smul (vecDeriv hG l k) (hC l))
    refine (S.congr_ae ?_).congr_ae_deriv ?_
    · filter_upwards [hval.coeFn_toLp] with x hx
      rw [hx]
      simp only [smul_eq_mul]
    · filter_upwards [hgrad.coeFn_toLp] with x hx
      rw [innerSL_apply_apply, hx]
      simp only [sum_inner, inner_smul_left, smul_eq_mul]
      simp [e, EuclideanSpace.inner_single_right, pd]
      exact Finset.sum_congr rfl fun l _ => by ring
  refine ⟨W1p.mk _ _ hw, ?_, Mf a c, ?_, fun φ => ?_⟩
  · rw [W1p.value_mk]
    filter_upwards [hval.coeFn_toLp] with x hx
    rw [hx]
    simp [PiLp.inner_apply, mul_comm]
  · exact contDiff_pi.2 fun i => contDiff_pi.2 fun k => contDiff_Mf ha hc i k
  · rw [W1p.gradient_mk]
    have hcore := core ha hc hdiv' hu hG hF heq φ
    have hφ := TF.of φ
    have e1 : ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x)
        ((hgrad.toLp _) x) = ∫ x, ∑ i, ∑ k, pd φ i x * (a x i k *
          ∑ l, (c x l * D x (e k) l + W1p.gradient v x l * pd (fun y => c y l) k x)) := by
      rw [integral_eq_setIntegral (fun x hx => by simp [(hφ.deriv _).zero_of_notMem hx])]
      refine integral_congr_ae ?_
      filter_upwards [hgrad.coeFn_toLp] with x hx
      rw [hx, matrixBilinearForm_eq_sum]
      simp only [gradient_coord]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      rw [sum_smul_e_apply]
    have e2 : ∫ x in (ballOpens : Set R3), ⟪c x, W1p.gradient Fw x⟫_ℝ * φ x =
        ∫ x, (∑ l, c x l * W1p.gradient Fw x l) * φ x := by
      rw [integral_eq_setIntegral (fun x hx => by simp [hφ.zero_of_notMem hx])]
      refine setIntegral_congr_fun ballOpens.isOpen.measurableSet fun x _ => ?_
      simp [PiLp.inner_apply, mul_comm]
    have e3 : ∫ x in (ballOpens : Set R3), matrixBilinearForm (Mf a c x)
        (gradient (φ : R3 → ℝ) x) (W1p.gradient v x) =
        ∫ x, ∑ i, ∑ k, pd φ i x * (Mf a c x i k * W1p.gradient v x k) := by
      rw [integral_eq_setIntegral (fun x hx => by simp [(hφ.deriv _).zero_of_notMem hx])]
      refine setIntegral_congr_fun ballOpens.isOpen.measurableSet fun x _ => ?_
      rw [matrixBilinearForm_eq_sum]
      simp only [gradient_coord]
    rw [e1, e2, e3]
    exact hcore

end OAI.AnisotropicCalderon.Regularity.DiffEq

namespace OAI.AnisotropicCalderon.Regularity
open TauCeti TauCeti.PDE EnergyBridge

/-- Let `v ∈ H²(B)` solve `-div(a ∇v) = F` weakly with `F ∈ H¹(B)`, and let `c` be a smooth
divergence-free vector field. Then `P v = ⟪c, ∇v⟫ ∈ H¹(B)` solves
`-div(a ∇(P v)) = ⟪c, ∇F⟫ - div(M ∇v)` weakly, for a smooth matrix field `M` (built from `a`, `c`
and their first derivatives). -/
theorem exists_diff_equation {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a)
    {c : R3 → R3} (hc : ContDiff ℝ ∞ c)
    (hdiv : ∀ x, ∑ l : Fin 3, fderiv ℝ c x (EuclideanSpace.single l 1) l = 0)
    (V : Wkp (volume : Measure R3) ballOpens 2 2) (Fw : W1p (volume : Measure R3) ballOpens 2)
    (heq : ∀ φ : 𝓓(ballOpens, ℝ),
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x)
          (W1p.gradient (Wkp.lowerOrder 1 V) x) =
        ∫ x in (ballOpens : Set R3), W1p.value Fw x * φ x) :
    ∃ w : W1p (volume : Measure R3) ballOpens 2,
      (⇑(W1p.value w) =ᵐ[(volume : Measure R3).restrict ballOpens]
        fun x => ⟪c x, W1p.gradient (Wkp.lowerOrder 1 V) x⟫_ℝ) ∧
      ∃ M : R3 → Matrix (Fin 3) (Fin 3) ℝ, ContDiff ℝ ∞ M ∧
        ∀ φ : 𝓓(ballOpens, ℝ),
          ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x)
              (W1p.gradient w x) =
            (∫ x in (ballOpens : Set R3), ⟪c x, W1p.gradient Fw x⟫_ℝ * φ x) +
              ∫ x in (ballOpens : Set R3), matrixBilinearForm (M x) (gradient (φ : R3 → ℝ) x)
                (W1p.gradient (Wkp.lowerOrder 1 V) x) := by
  have hG : HasWeakFDerivOn volume ballOpens (W1p.gradient (Wkp.lowerOrder 1 V))
      (Wkp.iteratedGradient 1 V) := by
    have h := Wkp.hasWeakFDerivOn_iteratedGradient 0 V
    rwa [Wkp.iteratedGradient_zero] at h
  exact DiffEq.main_abstract ha hc hdiv (Wkp.lowerOrder 1 V)
    (fun k l => ((EuclideanSpace.proj l : R3 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ R3 (DiffEq.e k))).comp_memLp' (Lp.memLp _)) hG Fw heq

end OAI.AnisotropicCalderon.Regularity
