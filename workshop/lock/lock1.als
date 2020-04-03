one sig Lock {code1,code2,code3:Int} {
    code1+code2+code3 in 0+1+2+3+4+5+6+7+8+9
}
enum Marker { C1,C2,C3 }

pred hint[c1,c2,c3, matched,wellPlaced : Int] {
    let codeDigits = Lock.(code1+code2+code3) |
    matched = #(
        (c1 in codeDigits => C1 else none) +
        (c2 in codeDigits => C2 else none) +
        (c3 in codeDigits => C3 else none)
    )
    wellPlaced = #(
        (c1=Lock.code1 => C1 else none) +
        (c2=Lock.code2 => C2 else none) +
        (c3=Lock.code3 => C3 else none)
    )
}

fact {
    hint[6,8,2, 1,1]
    hint[6,1,4, 1,0]
    hint[2,0,6, 2,0]
    hint[7,3,8, 0,0]
    hint[7,8,0, 1,0]
}

run {} for 5 int