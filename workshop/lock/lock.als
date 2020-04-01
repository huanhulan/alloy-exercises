// The puzzle is in challenge.jpg

pred lock[ a,b,c : Int ] {
    hint1[a,b,c]
    hint2[a,b,c]
    hint3[a,b,c]
    hint4[a,b,c]
    hint5[a,b,c]
}

pred hint1[a,b,c: Int] {
  (a=6 || (b!=8 && c!= 2)) 
  ||  (b=8 || (a!=6 && c!= 2))
  ||  (c=2 || (a!=6 && b!= 8)) 
}

pred hint2[a,b,c: Int] {
  a in 1+4 || (let x = b+c | x not in 1+6+4)
  || (b in 6+4 || (let x = a+c | x not in 1+6+4))
  || (c in 6+1 || (let x = a+b | x not in 1+6+4))
}

pred hint3[a,b,c: Int] {
  (a != 2 && b = 6 && c = 0)
  || (b != 0 && a=6 && c = 2)
  || (c != 6 && a=0 && b = 2)
}

pred hint4[a,b,c: Int] {
  all i: a + b + c |
    i not in 7 + 3 + 8
}

pred hint5[a,b,c: Int] {
  a in 0+8 || (let x = b+c | x not in 0+8+7)
  || (b in 0+7 || (let x = a+c | x not in 0+8+7))
  || (c in 7+8 || (let x = a+b | x not in 0+8+7))
}

run lock for 6 int