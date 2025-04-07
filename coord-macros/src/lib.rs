use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::quote;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input, punctuated::Punctuated, FnArg, Ident, ItemFn, Token,
};

/// A condition clause (e.g. `congruent(other, result)`).
struct Clause {
    kind: Ident,
    args: Punctuated<Ident, Token![,]>,
}

impl Parse for Clause {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let kind = input.parse()?;
        let content;
        syn::parenthesized!(content in input);
        // Parse a comma‑separated list of identifiers.
        let args = Punctuated::<Ident, Token![,]>::parse_terminated(&content)?;
        Ok(Clause { kind, args })
    }
}

/// A simple wrapper to allow parsing a comma‑separated list of `Ident`s.
struct IdentList(Punctuated<Ident, Token![,]>);

impl Parse for IdentList {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let punctuated = Punctuated::<Ident, Token![,]>::parse_terminated(input)?;
        Ok(IdentList(punctuated))
    }
}

/// Holds pre- and postconditions.
struct Conditions {
    pre: Vec<TokenStream2>,
    post: Vec<TokenStream2>,
}

impl Conditions {
    fn new() -> Self {
        Conditions {
            pre: Vec::new(),
            post: Vec::new(),
        }
    }
}

/// Process a single clause, adding assertions to `cond`.
fn process_clause(clause: Clause, has_self: bool, cond: &mut Conditions) {
    match clause.kind.to_string().as_str() {
        "congruent" => {
            let mut ids: Vec<Ident> = clause.args.into_iter().collect();
            let mut result_flag = false;
            // Remove any "result" identifier.
            ids.retain(|id| {
                if id == "result" {
                    result_flag = true;
                    false
                } else {
                    true
                }
            });
            // If the function is a method, ensure `self` is present.
            if has_self {
                let self_id = Ident::new("self", Span::call_site());
                if !ids.iter().any(|id| *id == self_id) {
                    ids.insert(0, self_id);
                }
            }
            // Generate pairwise assertions.
            for i in 0..ids.len() {
                for j in (i + 1)..ids.len() {
                    let a = &ids[i];
                    let b = &ids[j];
                    cond.pre.push(quote! {
                        assert!(#a.is_congruent_to(&#b), concat!(
                                "Precondition failed: ", stringify!(#a), " not congruent to ", stringify!(#b)
                        ));
                    });
                }
            }
            // If "result" was specified, add a postcondition.
            if result_flag && has_self {
                let self_id = Ident::new("self", Span::call_site());
                cond.post.push(quote! {
                    assert!(#self_id.is_congruent_to(&__result), concat!(
                        "Postcondition failed: result not congruent to ", stringify!(#self_id)
                    ));
                });
            }
        }
        "weakly_congruent" => {
            let mut ids: Vec<Ident> = clause.args.into_iter().collect();
            if has_self {
                let self_id = Ident::new("self", Span::call_site());
                if !ids.iter().any(|id| *id == self_id) {
                    ids.insert(0, self_id);
                }
            }
            if ids.len() == 2 {
                let a = &ids[0];
                let b = &ids[1];
                cond.pre.push(quote! {
                    assert!(#a.is_weakly_congruent_to(&#b), concat!(
                        "Precondition failed: ", stringify!(#a), " is not weakly congruent to ", stringify!(#b)
                    ));
                });
            }
        }
        "nonnullary" => {
            let ids: Vec<Ident> = clause.args.into_iter().collect();
            if ids.len() != 1 {
                panic!("nonnullary requires exactly one argument");
            }
            let arg = &ids[0];
            if arg == "result" {
                cond.post.push(quote! {
                    assert!(__result.rank() != 0, "Postcondition failed: result is rank 0");
                });
            } else {
                cond.pre.push(quote! {
                    assert!(#arg.rank() != 0, concat!(
                        "Precondition failed: ", stringify!(#arg), " is rank 0"
                    ));
                });
            }
        }
        _ => {}
    }
}

/// Rewrites the function body by injecting all conditions.
fn apply_conditions(func: &ItemFn, cond: Conditions) -> TokenStream2 {
    // Bind cond.pre and cond.post to local variables so they can be iterated.
    let pre = cond.pre;
    let post = cond.post;
    let body = &func.block;
    if post.is_empty() {
        quote! {{
            #(#pre)*
            #body
        }}
    } else {
        quote! {{
            #(#pre)*
            let __result = { #body };
            #(#post)*
            __result
        }}
    }
}

/// Common handler for #[requires(...)] and the other macros.
fn process_requires_impl(
    clauses: Punctuated<Clause, Token![,]>,
    func: ItemFn,
) -> TokenStream {
    let mut cond = Conditions::new();
    let has_self = matches!(func.sig.inputs.first(), Some(FnArg::Receiver(_)));
    for clause in clauses {
        process_clause(clause, has_self, &mut cond);
    }
    let new_body = apply_conditions(&func, cond);
    let mut func = func;
    func.block = syn::parse2(new_body).unwrap();
    TokenStream::from(quote! { #func })
}

/// The `requires` macro processes a comma‑separated list of clauses.
#[proc_macro_attribute]
pub fn requires(args: TokenStream, input: TokenStream) -> TokenStream {
    let clauses = parse_macro_input!(args with Punctuated::<Clause, Token![,]>::parse_terminated);
    let func = parse_macro_input!(input as ItemFn);
    process_requires_impl(clauses, func)
}

/// The `congruent` macro wraps its arguments in a single `congruent` clause.
#[proc_macro_attribute]
pub fn congruent(args: TokenStream, input: TokenStream) -> TokenStream {
    let idents = parse_macro_input!(args as IdentList).0;
    let clause = Clause {
        kind: Ident::new("congruent", Span::call_site()),
        args: idents,
    };
    let mut clauses = Punctuated::<Clause, Token![,]>::new();
    clauses.push(clause);
    let func = parse_macro_input!(input as ItemFn);
    process_requires_impl(clauses, func)
}

/// The `weakly_congruent` macro wraps its arguments in a single `weakly_congruent` clause.
#[proc_macro_attribute]
pub fn weakly_congruent(args: TokenStream, input: TokenStream) -> TokenStream {
    let idents = parse_macro_input!(args as IdentList).0;
    let clause = Clause {
        kind: Ident::new("weakly_congruent", Span::call_site()),
        args: idents,
    };
    let mut clauses = Punctuated::<Clause, Token![,]>::new();
    clauses.push(clause);
    let func = parse_macro_input!(input as ItemFn);
    process_requires_impl(clauses, func)
}

/// The `nonnullary` macro wraps its argument in a single `nonnullary` clause.
#[proc_macro_attribute]
pub fn nonnullary(args: TokenStream, input: TokenStream) -> TokenStream {
    let idents = parse_macro_input!(args as IdentList).0;
    if idents.len() != 1 {
        return syn::Error::new_spanned(idents, "nonnullary requires exactly one argument")
            .to_compile_error()
            .into();
    }
    let clause = Clause {
        kind: Ident::new("nonnullary", Span::call_site()),
        args: idents,
    };
    let mut clauses = Punctuated::<Clause, Token![,]>::new();
    clauses.push(clause);
    let func = parse_macro_input!(input as ItemFn);
    process_requires_impl(clauses, func)
}
