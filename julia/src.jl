abstract type Formula end
abstract type Compound <: Formula end
abstract type Unit <: Formula end
abstract type Literal <: Unit end

struct True <: Literal end
struct False <: Literal end

struct Atom <: Unit
	p::String
end

struct Neg <: Unit
	ϕ::Formula
end

struct And <: Compound
	ϕ₁::Formula
	ϕ₂::Formula
end

struct Or <: Compound
	ϕ₁::Formula
	ϕ₂::Formula
end

struct Imp <: Compound
	ϕ₁::Formula
	ϕ₂::Formula
end

function Base.show(io::IO, ϕ::Unit)
	if typeof(ϕ) == Neg
		if typeof(ϕ.ϕ) <: Unit
			print(io, '¬', ϕ.ϕ)
		else
			print(io, "¬(", ϕ.ϕ, ')')
		end
	else
		print(io, ϕ.p)
	end
end

function Base.show(io::IO, ϕ::Compound)
	if typeof(ϕ.ϕ₁) <: Unit
		print(io, ϕ.ϕ₁)
	else
		print(io, '(', ϕ.ϕ₁, ')')
	end

	if typeof(ϕ) == And
		print(io, '&')
	elseif typeof(ϕ) == Or
		print(io, '|')
	else
		print(io, '→')
	end

	if typeof(ϕ.ϕ₂) <: Unit
		print(io, ϕ.ϕ₂)
	else
		print(io, '(', ϕ.ϕ₂, ')')
	end
end

struct Sequent
	Φ::Array{Formula}
	ψ::Formula
end

¬ϕ = Neg(ϕ)
ϕ ∧ ψ = And(ϕ, ψ)
ϕ ∨ ψ = Or(ϕ, ψ)
ϕ → ψ = Imp(ϕ, ψ)

@enum Assoc LeftAssoc RightAssoc

PARENS = ["()", "[]"]
ATOM = r"^[A-Za-z][0-9]*$"
NEG = ["!"]
AND = ["&", "*"]
OR  = ["|", "+"]
IMP = ["->"]
SEQ = ["=>"]

function balanced_parens(ϕ, parens)
	c = 0
	for x ∈ ϕ
		if x == parens[1]
			c += 1
		elseif x == parens[2]
			c -= 1
			if c < 0
				return false
			end
		end
	end
	return c == 0
end

balanced_parens(ϕ) = all(balanced_parens(ϕ, parens) for parens ∈ PARENS)

function parse_unary(ϕ, Op, OP)
	for op ∈ OP
		if startswith(ϕ, op)
			return Op(parse_formula(ϕ[length(op)+1:end]))
		end
	end
end

function parse_binary(ϕ, Op, OP, assoc)
	for op ∈ OP
		splits = split(ϕ, op)
		e_range = (assoc == LeftAssoc ? reverse : identity)(1:length(splits)-1)
		for e ∈ e_range
			ϕ₁ = join(splits[1:e], op)
			ϕ₂ = join(splits[e+1:end], op)
			if balanced_parens(ϕ₁) && balanced_parens(ϕ₂)
				return Op(parse_formula(ϕ₁), parse_formula(ϕ₂))
			end
		end
	end
end

is_atomic(ϕ) = match(ATOM, ϕ) ≠ nothing
parse_neg(ϕ) = parse_unary(ϕ, Neg, NEG)
parse_and(ϕ) = parse_binary(ϕ, And, AND, LeftAssoc)
parse_or(ϕ)  = parse_binary(ϕ, Or, OR, LeftAssoc)
parse_imp(ϕ) = parse_binary(ϕ, Imp, IMP, RightAssoc)

function converge(subject, functions)
	while true
		subject_old = subject
		for f ∈ functions
			subject = f(subject)
		end
		if subject_old == subject
			return subject
		end
	end
end

strip_parens(ϕ, parens) = !isempty(ϕ) && ϕ[[1, end]] == parens ? ϕ[2:end-1] : ϕ
strip_parens(ϕ) = converge(ϕ, [ϕ -> strip_parens(ϕ, parens) for parens ∈ PARENS])
strip_formula(ϕ) = converge(ϕ, [strip, strip_parens])

function input(prompt="")
	print(prompt)
	return chomp(readline())
end

function continue_abort()
	while true
		inp = input("[C]ontinue/[A]bort? ")
		if inp == "c" || inp == "C"
			break
		elseif inp == "a" || inp == "A"
			println("Aborting")
			exit()
		end
	end
end

function parse_formula(ϕ)
	ϕ = strip_formula(ϕ)
	for p in [parse_imp, parse_or, parse_and, parse_neg]
		if (ϕ⁺ = p(ϕ)) ≠ nothing
			return ϕ⁺
		end
	end
	if !is_atomic(ϕ)
		println("Following will be regarded as an atomic proposition: >$ϕ<")
		continue_abort()
	end
	return Atom(ϕ)
end

function parse_sequent(Δ)
	Φ = ""
	ψ = Δ
	for seq ∈ SEQ
		splits = split(Δ, seq)
		if length(splits) == 2
			Φ, ψ = splits
			break
		end
		if length(splits) > 2
			println("Multiple $seq symbols detected")
			continue_abort()
		end
	end
	Φ = map(parse_formula, split(Φ, ',', keepempty=false))
	ψ = parse_formula(ψ)
	Sequent(Φ, ψ)
end

struct ProofStep
	level::Int
	ϕ::Formula
	rationale::String
end

mutable struct Proof
	steps::Array{ProofStep}
	current_level::Int
end

function accessible(Γ::Proof, target::Int)
	if target > length(Γ.steps) || Γ.current_level < target
		return false
	end
	for i ∈ target:length(Γ.steps)
		if Γ.steps[i].level < Γ.steps[target].level
			return false
		end
	end
	return true
end

Γ::Proof ≡ target::Int = accessible(Γ, target)
Base.getindex(Γ::Proof, i::Int64) = Γ.steps[i]
(Γ::Proof)(i::Int64) = Γ[i].ϕ

function add_step(Γ, ϕ, rationale)
	push!(Γ.steps, ProofStep(Γ.current_level, ϕ, rationale))
end

function andi(Γ::Proof, i, j)
	if Γ ≡ i && Γ ≡ j
		add_step(Γ, Γ(i) ∧ Γ(j), "∧ᵢ, $i, $j")
	end
end

function ande1(Γ, i)
	if Γ ≡ i
		ϕ = Γ(i)
		if typeof(ϕ) == And
			add_step(Γ, ϕ.ϕ₁, "∧ₑ₁, $i")
		end
	end
end

function ande2(Γ, i)
	if Γ ≡ i
		ϕ = Γ(i)
		if typeof(ϕ) == And
			add_step(Γ, ϕ.ϕ₂, "∧ₑ₂, $i")
		end
	end
end

# TODO

function ori1(Γ, i, ψ)
	if i ≤ length(Γ)
		if !(typeof(ψ) <: Formula)
			ψ = parse_formula(ψ)
		end
		[Γ; ProofStep(1, Γ[i].ϕ ∨ ψ, "∨ᵢ₁ $i")]
	end
end

function ori2(Γ, i, ψ)
	if i ≤ length(Γ)
		if !(typeof(ψ) <: Formula)
			ψ = parse_formula(ψ)
		end
		[Γ; ProofStep(1, ψ ∨ Γ[i].ϕ, "∨ᵢ₂ $i")]
	end
end

function ore(Γ, i, J, K)
	if i > length(Γ)
		return
	end

	ϕ = Γ[i].ϕ
	if typeof(ϕ) ≠ Or
		return
	end

	j₁, j₂ = J
	k₁, k₂ = K

	return [Γ; ProofStep(1, Γ[j₂].ϕ, "∨ₑ, $i, $j₁-$j₂, $k₁-$k₂")]
end

function impi(Γ, I)
	i₁, i₂ = I
	return [Γ; ProofStep(1, Γ[i₁].ϕ → Γ[i₂].ϕ, "→ᵢ, $i₁-$i₂")]
end

function impe(Γ, i, j)
	return [Γ; ProofStep(1, Γ[j].ϕ.ϕ₂, "→ₑ, $i, $j")]
end

function negi(Γ, I)
	i₁, i₂ = I
	return [Γ; ProofStep(1, ¬Γ[i₁].ϕ, "¬ᵢ, $i₁-$i₂")]
end

function nege(Γ, i, j)
	return [Γ; ProofStep(1, False(), "¬ₑ, $i, $j")]
end

function bote(Γ, i, ψ)
	if !(typeof(ψ) <: Formula)
		ψ = parse_formula(ψ)
	end
	return [Γ; ProofStep(1, ψ, "⊥ₑ, $i")]
end

function negnegi(Γ, i)
	return [Γ; ProofStep(1, ¬¬Γ[i].ϕ, "¬¬ᵢ, $i")]
end
	
function negnege(Γ, i)
	return [Γ; ProofStep(1, Γ[i].ϕ.ϕ.ϕ, "¬¬ₑ, $i")]
end

function MT(Γ, i, j)
	return [Γ; ProofStep(1, ¬Γ[i].ϕ.ϕ₁, "MT, $i, $j")]
end

function PBC(Γ, I)
	i₁, i₂ = I
	return [Γ; ProofStep(1, Γ[i₁].ϕ.ϕ, "PBC, $i₁, $i₂")]
end

function LEM(Γ, ψ)
	if !(typeof(ψ) <: Formula)
		ψ = parse_formula(ψ)
	end
	return [Γ; ProofStep(1, ψ ∨ ¬ψ, "LEM")]
end

nd_rules = String.(Symbol.((andi, ande1, ande2,
							ori1, ori2, ore,
							impi, impe,
							negi, nege,
							bote,
							negnegi, negnege,
							MT, PBC, LEM)))

function prompt_nd()
	inp = input("Natural deduction: ")
	nd = map(strip, split(inp, r",|\s+", keepempty=false))
	rule = nd[1]
	args = nd[2:end]
	
	if rule ∉ nd_rules
		println("Unknown rule >", rule, "<, please retry")
		return prompt_nd()
	end

	return eval(Symbol(rule)), map(x -> parse(Int, x), args)
end

function Base.show(io::IO, γ::ProofStep)
	print(io, γ.ϕ, " (", γ.rationale, ")")
end

function Base.show(io::IO, Γ::Array{ProofStep})
	for (i, γ) ∈ enumerate(Γ)
		println(i, ". ", γ)
	end
end

function clear()
	run(`cmd /c cls`)
	# println("\33[2J")
end

function main(args)
	clear()
	Δ = parse_sequent(input("Sequent: "))

	Γ = ProofStep[ProofStep(1, ϕ, "Premise") for ϕ ∈ Δ.Φ]
	while true
		clear()
		println("== Working Proof ==")
		print(Γ)
		println("== Target ==")
		println(Δ.ψ)
		if Δ.ψ ∈ (γ.ϕ for γ in Γ)
			println("Target reached!")
			break
		end
		nd_rule, nd_args = prompt_nd()
		Γ = nd_rule(Γ, nd_args...)
	end
end

main(ARGS)

# println(parse_sequent(length(ARGS) ≥ 1 ? ARGS[1] : "a & b"))
