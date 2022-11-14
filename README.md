# RKM

At the moment, the goal of this project is just to have fun. Nothing else.

# Sample Snippet

```
data List a =
  | Cons a (List a)
  | Nil

def pack (x : a) (y : b) = (x, y)
def tail (list : List a) =
  match list with
    | Cons _ xs -> xs
    | Nil -> Nil
```

# Grammar

## Comment

You are either a line comment that starts with `//`, which ignores the rest of the line, or a block comment that starts with `/*`, ends with `*/`, and is nested.

## Token

### Operators

These are sequences with special fixed meaning in the program. Here is a table of all of them.

```
+   <   ==  ->  :   .
-   >   !=  |   ::
*   <=  =   !   ,
/   >=  (   )   ;
```

### Keywords

These have special fixed meaning in the program. Here is a table of all of them.

```
type    data    def     let     match   if
then    else    and     or      in      true
false   _
```

### Numeric Literals

These are numbers. In addition to the decimal base, which cannot have multiple leading zeros, several other bases are supported: binary via `0b` or `0B`, octal via `0c` or `0C`, and hexadecimal via `0x` or `0X`. The underscore is used as a digit separator. Every digit separator must be followed by a digit.

### Identifiers

Identifiers begin with letters or an underscore and are followed by optionally many characters composed from alphanumeric characters and underscores. They must also be not one of the keywords listed above.

Somewhat confusingly, there are two classes of identifiers. One is for constructors, which must begin with an uppercase letter. The other is for everything else, which must begin with anything other than an uppercase letter.

### Character Literals

Character literals are surrounded with single quotes (`'`) and contain a single unicode scalar value. Note that single quotes and several other special characters must be escaped via backslashes.

### String Literals

String literals are surrounded with double quotes (`"`) and contain optionally many unicode scalar values UTF-8 encoded. Double quotes and several other special characters must be escaped via backslashes.

## Top-level Definition

### Data Definition

_defn_ &longrightarrow; `data` **[Constructor Identifier]** **[General Identifier]**<sup>\*</sup> `=` `|`<sup>?</sup> _case_ ( `|` _case_ )<sup>\*</sup><br/>
_case_ &longrightarrow; **[Constructor Identifier]** ( _type<sub>2</sub>_ )<sup>\*</sup>

### Type Alias

_defn_ &longrightarrow; `type` **[Constructor Identifier]** **[General Identifier]**<sup>\*</sup> `=` _type<sub>0</sub>_

### Value Definition

_defn_ &longrightarrow; `def` **[General Identifier]** _pattern<sub>3</sub>_<sup>\*</sup> ( `:` _type<sub>0</sub>_ )<sup>?</sup> `=` _expr<sub>0</sub>_

## Type

### Tuple Type

_type<sub>-1</sub>_ &longrightarrow; ( _type<sub>0</sub>_ `,` )<sup>+</sup> _type<sub>0</sub>_<sup>?</sup><br/>
_type<sub>-1</sub>_ &longrightarrow; _type<sub>0</sub>_

### Function Type

_type<sub>0</sub>_ &longrightarrow; _type<sub>1</sub>_ `->` _type<sub>0</sub>_

### Type Application

_type<sub>1</sub>_ &longrightarrow; _type<sub>1</sub>_ _type<sub>2</sub>_

### Primary Type

_type<sub>2</sub>_ &longrightarrow; `(` _type<sub>-1</sub>_<sup>?</sup> `)`<br/>
_type<sub>2</sub>_ &longrightarrow; **[Identifier]**<br/>
_type<sub>2</sub>_ &longrightarrow; `_`

## Pattern

### Tuple Pattern

_pattern<sub>-1</sub>_ &longrightarrow; ( _pattern<sub>0</sub>_ `,` )<sup>+</sup> _pattern<sub>0</sub>_<sup>?</sup><br/>
_pattern<sub>-1</sub>_ &longrightarrow; _pattern<sub>0</sub>_

### Alternate Pattern

_pattern<sub>0</sub>_ &longrightarrow; _pattern<sub>0</sub>_ `|` _pattern<sub>1</sub>_<br/>
_pattern<sub>0</sub>_ &longrightarrow; _pattern<sub>1</sub>_

### Data Deconstruction Pattern

_pattern<sub>1</sub>_ &longrightarrow; **[Constructor Identifier]** ( _pattern<sub>2</sub>_ )<sup>\*</sup><br/>
_pattern<sub>1</sub>_ &longrightarrow; _pattern<sub>2</sub>_

### Type Constrainted Pattern

_pattern<sub>2</sub>_ &longrightarrow; _pattern<sub>3</sub>_ `:` _type<sub>0</sub>_<br/>
_pattern<sub>2</sub>_ &longrightarrow; _pattern<sub>3</sub>_

### Primary Pattern

_pattern<sub>3</sub>_ &longrightarrow; `(` _pattern<sub>-1</sub>_<sup>?</sup> `)`<br/>
_pattern<sub>3</sub>_ &longrightarrow; **[General Identifier]**<br/>
_pattern<sub>3</sub>_ &longrightarrow; `true`<br/>
_pattern<sub>3</sub>_ &longrightarrow; `false`<br/>
_pattern<sub>3</sub>_ &longrightarrow; `+`<sup>?</sup> **[Numeric Literal]**<br/>
_pattern<sub>3</sub>_ &longrightarrow; `-` **[Numeric Literal]**<br/>
_pattern<sub>3</sub>_ &longrightarrow; **[Character Literal]**<br/>
_pattern<sub>3</sub>_ &longrightarrow; **[String Literal]**<br/>
_pattern<sub>3</sub>_ &longrightarrow; `_`

## Expression

### Sequence Expression

_expr<sub>-2</sup>_ &longrightarrow; ( _expr<sub>-1</sub>_ `;` )<sup>+</sup> _expr<sub>-1</sub>_<sup>?</sup><br/>
_expr<sub>-2</sup>_ &longrightarrow; _expr<sub>-1</sub>_

### Tuple Expression

_expr<sub>-1</sup>_ &longrightarrow; ( _expr<sub>0</sub>_ `,` )<sup>+</sup> _expr<sub>0</sub>_<sup>?</sup><br/>
_expr<sub>-1</sup>_ &longrightarrow; _expr<sub>0</sub>_

### Binding Expression

_expr<sub>0</sub>_ &longrightarrow; `let` _binding_ ( `;` _binding_ )<sup>\*</sup> `;`<sup>?</sup> `in` _expr<sub>0</sub>_<br/>
_binding_ &longrightarrow; _pattern<sub>0</sub>_ `=` _expr<sub>0</sub>_

### Match Expression

_expr<sub>0</sub>_ &longrightarrow; `match` _expr<sub>0</sub>_ `with` `|`<sup>?</sup> _case_ ( `|` _case_ )<sup>\*</sup><br/>
_case_ &longrightarrow; _pattern<sub>0</sub>_ `->` _expr<sub>0</sub>_

### If-else Expression

_expr<sub>0</sub>_ &longrightarrow; `if` _expr<sub>0</sub>_ `then` _expr<sub>0</sub>_ `else` _expr<sub>0</sub>_<br/>
_expr<sub>0</sub>_ &longrightarrow; _expr<sub>1</sub>_

### Or Expression

_expr<sub>1</sub>_ &longrightarrow; _expr<sub>1</sub>_ `or` _expr<sub>2</sub>_<br/>
_expr<sub>1</sub>_ &longrightarrow; _expr<sub>2</sub>_

### And Expression

_expr<sub>2</sub>_ &longrightarrow; _expr<sub>2</sub>_ `and` _expr<sub>3</sub>_<br/>
_expr<sub>2</sub>_ &longrightarrow; _expr<sub>3</sub>_

### Relational Expression

_expr<sub>3</sub>_ &longrightarrow; _expr<sub>3</sub>_ `<` _expr<sub>4</sub>_<br/>
_expr<sub>3</sub>_ &longrightarrow; _expr<sub>3</sub>_ `>` _expr<sub>4</sub>_<br/>
_expr<sub>3</sub>_ &longrightarrow; _expr<sub>3</sub>_ `<=` _expr<sub>4</sub>_<br/>
_expr<sub>3</sub>_ &longrightarrow; _expr<sub>3</sub>_ `>=` _expr<sub>4</sub>_<br/>
_expr<sub>3</sub>_ &longrightarrow; _expr<sub>3</sub>_ `==` _expr<sub>4</sub>_<br/>
_expr<sub>3</sub>_ &longrightarrow; _expr<sub>3</sub>_ `!=` _expr<sub>4</sub>_<br/>
_expr<sub>3</sub>_ &longrightarrow; _expr<sub>4</sub>_

### Additive Expression

_expr<sub>4</sub>_ &longrightarrow; _expr<sub>4</sub>_ `+` _expr<sub>5</sub>_<br/>
_expr<sub>4</sub>_ &longrightarrow; _expr<sub>4</sub>_ `-` _expr<sub>5</sub>_<br/>
_expr<sub>4</sub>_ &longrightarrow; _expr<sub>5</sub>_

### Multiplicative Expression

_expr<sub>5</sub>_ &longrightarrow; _expr<sub>5</sub>_ `*` _expr<sub>6</sub>_<br/>
_expr<sub>5</sub>_ &longrightarrow; _expr<sub>5</sub>_ `/` _expr<sub>6</sub>_<br/>
_expr<sub>5</sub>_ &longrightarrow; _expr<sub>6</sub>_

### Application Expression

_expr<sub>6</sub>_ &longrightarrow; _expr<sub>6</sub>_ _expr<sub>7</sub>_<br/>
_expr<sub>6</sub>_ &longrightarrow; _expr<sub>7</sub>_

### Typed Expression

_expr<sub>7</sub>_ &longrightarrow; _expr<sub>8</sub>_ `:` _type<sub>0</sub>_<br/>
_expr<sub>7</sub>_ &longrightarrow; _expr<sub>8</sub>_

### Prefix Expression

_expr<sub>8</sub>_ &longrightarrow; `+` _expr<sub>8</sub>_<br/>
_expr<sub>8</sub>_ &longrightarrow; `-` _expr<sub>8</sub>_<br/>
_expr<sub>8</sub>_ &longrightarrow; `!` _expr<sub>8</sub>_<br/>
_expr<sub>8</sub>_ &longrightarrow; _expr<sub>9</sub>_

### Attribute Expression

_expr<sub>9</sub>_ &longrightarrow; _expr<sub>9</sub>_ `.` **[Identifier]**<br/>
_expr<sub>9</sub>_ &longrightarrow; _expr<sub>10</sub>_

### Primary Expression

_expr<sub>10</sub>_ &longrightarrow; `(` _expr<sub>-2</sub>_<sup>?</sup> `)`<br/>
_expr<sub>10</sub>_ &longrightarrow; **[Identifier]**<br/>
_expr<sub>10</sub>_ &longrightarrow; `true`<br/>
_expr<sub>10</sub>_ &longrightarrow; `false`<br/>
_expr<sub>10</sub>_ &longrightarrow; **[Numeric Literal]**<br/>
_expr<sub>10</sub>_ &longrightarrow; **[Character Literal]**<br/>
_expr<sub>10</sub>_ &longrightarrow; **[String Literal]**
