open util/ordering[River]
open util/ordering[Journey]

abstract sig Cargo {}

sig Fox, Chicken, Grain extends Cargo {}

sig Bank {}

sig River {
	leftBank : one Bank,
	rightBank : one Bank,
	allCargo: set Cargo,
    farmerLoc: one Bank,
	group: (leftBank + rightBank) one -> allCargo,
    journey: lone Journey
} {
	allCargo in (leftBank.group + rightBank.group)
	leftBank != rightBank
    farmerLoc in (rightBank + leftBank)
}

sig Journey {
	cargo: lone Cargo,
	bankFrom: one Bank,
	bankTo: one Bank
}

pred allCargoBelongsToARiver {
	no c: Cargo | no allCargo.c
}

pred allCargoLeftBank[r: River] {
	#r.group[r.rightBank] = 0
}

pred allCargoRightBank[r: River] {
	#r.group[r.leftBank] = 0
}

pred oneOfEachCargo[r: River] {
	#{ c: r.allCargo | c in Fox } = 1
	#{ c: r.allCargo | c in Chicken } = 1
	#{ c: r.allCargo | c in Grain } = 1
}

pred journeySafe[r': River, j: Journey] {
	(Fox + Chicken) not in j.bankFrom.(r'.group)
	(Grain + Chicken) not in j.bankFrom.(r'.group)
}

pred doJourney[r, r': River] {
    let j = r.journey {
        journeySafe[r', j]
        j.bankFrom = r.farmerLoc
        j.bankTo = r.leftBank + r.rightBank - r.farmerLoc
        r'.farmerLoc = j.bankTo
        r.rightBank = r'.rightBank
        r.leftBank = r'.leftBank
        some j.cargo => j.cargo in j.bankFrom.(r.group)
        j.bankFrom.(r'.group) = j.bankFrom.(r.group) - j.cargo
        j.bankTo.(r'.group) = j.bankTo.(r.group) + j.cargo
    }
}

pred solveProblem {
	allCargoBelongsToARiver
    oneOfEachCargo[first]
    allCargoLeftBank[first]
    allCargoRightBank[last]
    all r: River, r': r.next {
        doJourney[r, r']
    }
}

run solveProblem for exactly 5 Journey, 8 River, 2 Bank, 3 Cargo
