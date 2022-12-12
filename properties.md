- [ ] last(append(t, x)) == x
- [ ] head(prepend(t, x)) == x

- [ ] tolist(append(t, x)) == tolist(t) ++ x
- [ ] tolist(prepend(t, x)) == x ++ tolist(t)
- [ ] tolist(concat(t1, t2)) == tolist(t1) ++ tolist(t2)

- [ ] head(concat(empty, t2)) == head(t2)
- [ ] head(concat(t2, empty)) == getfirst(t2)
- [ ] last(concat(empty, t2)) == last(t2)
- [ ] last(concat(t2, empty)) == last(t2)

- [ ] (a, b, c) = split(pred, t) ; tolist(t) == a ++ b ++ c

- [ ] isempty(concat(empty, t)) == isempty(t)
- [ ] isempty(concat(t, empty)) == isempty(t)
- [ ] isempty(concat(t1, t2)) == isempty(t1) && isempty(t2)
- [ ] isempty(empty) == true
- [ ] isempty(!= empty) == false
