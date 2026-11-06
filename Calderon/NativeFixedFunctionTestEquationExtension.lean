import TauCeti.Analysis.PDE.DirichletProblem

/-! See upfront EXPANSION.json: the pinned compact-test density argument needs no zero membership of the fixed function. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open TauCeti TauCeti.PDE
variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

lemma native_energy_equation_of_forall_testFunction
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p mu Omega 2)
    (h : ∀ phi : 𝓓(Omega, ℝ),
      energyFormH1 a b c u (W1p.ofTestFunctionₗ mu Omega 2 phi) =
        ∫ x in Omega, f x * phi x ∂mu) :
    ∀ v : W1p0 mu Omega 2,
      energyFormH1 a b c u (v : W1p mu Omega 2) = dirichletForcing f v := by
  have hforce : ∀ phi : 𝓓(Omega, ℝ),
      ⟪f, W1p.value (W1p.ofTestFunctionₗ mu Omega 2 phi)⟫_ℝ =
        ∫ x in Omega, f x * phi x ∂mu := fun phi => by
    have hf := dirichletForcing_apply_eq_setIntegral f
      ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule (p := 2) phi⟩
    rw [dirichletForcing_apply] at hf
    refine hf.trans (integral_congr_ae ?_)
    filter_upwards [testFunctionLp_apply_ae (mu := mu) 2 phi] with x hx
    rw [W1p.value_ofTestFunctionₗ, hx]
  have hclosed : IsClosed {v : W1p mu Omega 2 |
      energyFormH1L hcoeff u v = ⟪f, W1p.value v⟫_ℝ} :=
    isClosed_eq (energyFormH1L hcoeff u).continuous
      (((innerSL ℝ f).continuous.comp W1p.valueL.continuous).congr fun v => by
        simp only [Function.comp_apply, innerSL_apply_apply]
        exact congrArg _ (W1p.valueL_apply v))
  intro v
  have hmem := w1p0Submodule_subset_of_isClosed hclosed
    (fun phi => by simpa only [Set.mem_ofPred_eq, energyFormH1L_apply, hforce] using h phi) v.2
  rw [dirichletForcing_apply, ← energyFormH1L_apply hcoeff]
  exact hmem

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.native_energy_equation_of_forall_testFunction
