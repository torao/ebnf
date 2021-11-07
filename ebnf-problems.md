# The Problems of Extended BNF

### definition-list

The definition-list (OR condition) is unclear as to what action should be taken in cases where multiple conditions are matched.

In definition-list, it possibly have to buffer the whole stream to make a decision if it uses a schema that leaves very long conditition in the OR branch.
For instance,

```ebnf
A = {'a'};
FINALLY NOT A = {'a'}, 'b';
S = A | FINALLY NOT A;
```

where it need to read and buffer the input `aaaaaa...b` to the end of the stream to determine whether it matches `A` or `FINALLY NOT A`.
