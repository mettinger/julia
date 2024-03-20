using Metatheory
using Metatheory.EGraphs
using Metatheory.Library

mutable struct Category
    src::Dict
    target::Dict
    relations
end

# Initialize a category and test it 
function categoryInit(src::Dict, target::Dict, relations)

    identity = @theory f begin
        1 ∘ f == f 
        f ∘ 1 == f
    end
    
    cat = Category(src, target, relations);
    if checkComposability(cat, true)
        if checkComposition(cat, true)
            if checkAssociativity(cat, true)
                cat.relations = cat.relations ∪ identity
                return cat
            end
        end
    end
end;

#Check that all the composables defined by equations have matching targets and sources.
function checkComposability(c::Category, debug::Bool=false)
    for thisEquality in c.relations
        second, first = thisEquality.left.args 
        
        if c.src[second] != c.target[first]
            if debug
                println("composability violation")
                println(first,second)
                println(" ")
            end
            return false
        end
    end
    return true
end

# Compose arrows j and i and then simplify to a name
function simplifyComposition(i::Symbol, j::Symbol, c::Category) :: Symbol
    expression = :($j ∘ $i) 

    g = EGraph(expression)
    saturate!(g, c.relations)
    simplified = extract!(g, astsize)
    return simplified
end

# Check that category c satisfies associativity by brute force
function checkAssociativity(c::Category, debug::Bool = false) :: Bool
    morphisms = keys(c.src)
 
    for i in morphisms
        for j in morphisms
            for k in morphisms
                if (c.target[i] == c.src[j]) && (c.target[j] == c.src[k])
                    leftAssocLeft = simplifyComposition(i, j, c)
                    leftAssoc = simplifyComposition(leftAssocLeft, k, c)
                    rightAssocRight = simplifyComposition(j, k, c)
                    rightAssoc = simplifyComposition(i, rightAssocRight, c)
                    if leftAssoc != rightAssoc
                        if debug
                            print("associativity violation: ")
                            println(i,j,k)
                            println(leftAssocLeft)
                            println(leftAssoc)
                            println(rightAssocRight)
                            println(rightAssoc)
                            println(" ")
                        end

                        return false
                    end
                end
            end
        end
    end

    return true
end;

#Check that the composition of any two arrows with matching sources and targets has a name by brute force
function checkComposition(c::Category, debug::Bool=false) :: Bool
    
    morphisms = keys(c.src)
    leftSides = Set([string(thisEquality.left) for thisEquality in c.relations])

    for i in morphisms
        for j in morphisms
            if c.target[i] == c.src[j]
                thisComposition = :($j ∘ $i)
                if !in(string(thisComposition), leftSides) # check if composition is a left side of some equation
                    if debug
                        println("missing composition name: ")
                        println(i,j)
                        println(" ")
                    end
                    return false
                end
            end
        end
    end
    return true
end;

src = Dict(:f => 0, :g => 1, :h => 2, :i => 0, :k => 1, :m => 0, :n => 0)
target = Dict(:f => 1, :g => 2, :h => 3, :i => 2, :k => 3, :m => 3, :n => 3)

relations = @theory begin
    :g ∘ :f == :i 
    :h ∘ :g == :k
    :h ∘ :i == :m 
    :k ∘ :f == :m 
end

myCat = categoryInit(src, target, relations);

function productCategory(c::Category, d::Category)
    src = srcProduct(c, d)
    target = targetProduct(c, d)
    relations = relationsProduct(c, d)
    productCat = categoryInit(src, target, relations)
    return productCat
end;

function srcProduct(c::Category, d::Category)
    srcKeys = [(i, j) for i in keys(c.src) for j in keys(d.src)]
    srcValues = [(i, j) for i in values(c.src) for j in values(d.src)]
    return Dict(zip(srcKeys, srcValues))
end

function targetProduct(c::Category, d::Category)
    targetKeys = [(i, j) for i in keys(c.target) for j in keys(d.target)]
    targetValues = [(i, j) for i in values(c.target) for j in values(d.target)]
    return Dict(zip(targetKeys, targetValues))
end

function relationsProduct(c::Category, d::Category)
    relations = Vector{EqualityRule}([])
    for cRelation in c.relations
        for dRelation in d.relations
            thisRelation = @rule ($(cRelation.left.args[1]), $(dRelation.left.args[1])) ∘ ($(cRelation.left.args[2]), $(dRelation.left.args[2]))  == ($(cRelation.right), $(dRelation.right))
            push!(relations, thisRelation)
        end
    end
    return relations
end;

cat1 = categoryInit(src, target, relations);
cat2 = categoryInit(src, target, relations);

cat1CrossCat2 = productCategory(cat1, cat2)

using NBInclude
nbexport("categories.jl", "categories.ipynb")