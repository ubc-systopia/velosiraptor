# Conventions

In the language specification we use the following conventions to express the language.

**Whitespace**
The VelosiRaptor language is *not* whitespace sensitive. The grammar is expressed in terms
of non-whitespace tokens.

**Rule**
We define rules using uppercase letters and an assignment operator.
The following defines a rule with a single body.

```
RULEID := RULE_BODY
```

**Alternatives**
Alternative rule components are separated using the pipe `|` operator.
For example, the following rule matches either rule body `A` or `A`.

```
RULEID := RULE_BODY_A | RULE_BODY_B
```
The first alternative that matches will be taken.

**Subrules**
Parts of the rule body can be grouped together using square brackets. Here the rule
matches a `A_1` or `A_2` followed by `B`
```
RULEID := [ RULE_A_1 | RULE_A_2 ] RULE_B
```

**Repetitions**
Subrules can be repeated using the `+` operator indicating one or more occurrences of the
subrule, and `*` operator for zero or more. The following has at least one occurrence of
rule body `A`, and zero or more of rule body `B`.
```
RULEID := [ RULE_BODY_A ]+ [RULE_BODY_B]*
```

**Optional Subrules**
To denote a subrule that may be left out the question mark operator `?` is used.\
Here, the rule body `A` is optional.
```
RULEID := RULE_BODY_A? RULE_BODY_B
```

**Special Rules**
To recognize the end of line explicitly where needed, the `EOL` rule is used.

```
EOL
```

To match any element until the next subrule is met, the `ANY` rule is used.
```
ANY
```

