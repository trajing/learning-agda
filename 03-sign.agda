data Sign : Set where
  + : Sign
  - : Sign

_*_ : Sign → Sign → Sign
+ * x = x
- * + = -
- * - = +
