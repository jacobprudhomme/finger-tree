- [x] last(append(t, x)) == x
- [x] t.addL(x).headL == x

- [x] tolist(append(t, x)).last ==  x
- [x] tolist(prepend(t, x)).head == x
- [ ] tolist(concat(t1, t2)) == tolist(t1) ++ tolist(t2)
- [x] concat(t1, t2).headL == t1.headL.orElse(t2.headL)
- [x] concat(t1, t2).headR == t2.headR.orElse(t1.headR)

- [x] headL(concat(empty, t2)) == headL(t2)
- [x] headR(concat(t2, empty)) == headR(t2)
- [ ] last(concat(empty, t2)) == last(t2)
- [ ] last(concat(t2, empty)) == last(t2)

- [ ] (a, b, c) = split(pred, t) ; tolist(t) == a ++ b ++ c

- [x] isempty(concat(empty, t)) == isempty(t)
- [x] isempty(concat(t, empty)) == isempty(t)
- [x] isempty(concat(t1, t2)) == isempty(t1) && isempty(t2)
- [x] isempty(empty) == true
- [x] isempty(!= empty) == false

- [ ] toTree(l).toList() == l
