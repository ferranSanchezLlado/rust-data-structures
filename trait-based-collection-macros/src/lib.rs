//! This crate provides all the procedural macros that are used in the [`trait_based_collection`]
//! crate. These macros are used to generate the boilerplate code that is commonly required in the
//! implementation of a new [`Collection`].
//!
//! This crate contains the following derivable macros:
//! - [`FromIterator`](crate::FromIterator)
//! - [`IntoIterator`](crate::IntoIterator)
//! - [`Default`](crate::Default)
//! - [`Extend`](crate::Extend)
//! - [`Display`](crate::Display)
//! - [`NewMacro`](crate::NewMacro)
//! - [`Drop`](crate::Drop)
//! - [`Index`](crate::Index)
//! - [`All`](crate::All)
//!
//! This crate contains the following procedural macros:
//! - [`internal_check_expansion_add`](macro@crate::internal_check_expansion_add)
//! - [`check_expansion_add`](macro@crate::check_expansion_add)
//! - [`iterator`](macro@crate::iterator)
//!
//! [`trait_based_collection`]: ../trait_based_collection/index.html
//! [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
#![warn(missing_docs)]
use convert_case::{Case, Casing};
use proc_macro::TokenStream;
use proc_macro2::Group;
use quote::__private::TokenTree;
use quote::{format_ident, quote, ToTokens};
use std::collections::HashSet;
use syn::__private::TokenStream2;
use syn::parse::{Parse, ParseStream, Result};
use syn::{parse_quote, Block, DeriveInput, FnArg, Ident, ItemFn, Pat, Token};

/// This macro is used to derive the [`FromIterator`] a standard implementation for all the data
/// structures that implement the [`Collection`] trait. This macro will automatically take into
/// account the size of the iterator and create a new instance of the data structure with the
/// appropriate capacity. This is useful for collections that have a fixed size (that implement the
/// [`FixedSizeCollection`] trait) as it will prevent the collection from having to resize itself
/// multiple times.
///
/// # Panics
/// This macro will panic if the input could not be properly parsed using the [`syn`] crate.
///
/// [`FromIterator`]: std::iter::FromIterator
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
/// [`FixedSizeCollection`]: ../trait_based_collection/collection/trait.FixedSizeCollection.html
#[proc_macro_derive(FromIterator)]
pub fn from_iterator_collection(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).expect("Could not parse input");

    impl_derive_from_iterator(&ast)
}

/// Internal function that implements the [`FromIterator`] trait for all the data structures that
/// implement the [`Collection`] trait. This function is used by the crates
/// [`FromIterator`](crate::FromIterator) and [`All`](crate::All) macros.
///
/// [`FromIterator`]: std::iter::FromIterator
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
fn impl_derive_from_iterator(ast: &DeriveInput) -> TokenStream {
    let name = &ast.ident;

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();
    let types = ast.generics.type_params().collect::<Vec<_>>();
    assert!(
        !types.is_empty(),
        "#[derive(FromIterator)] needs at least one type parameter"
    );
    let ty = &types[0].ident;

    let gen = quote! {
        impl #impl_generics FromIterator<#ty> for #name #ty_generics #where_clause {
            fn from_iter<I: IntoIterator<Item = #ty>>(iter: I) -> Self {
                let mut iter = iter.into_iter();

                let (min, max) = iter.size_hint();
                let mut collection = if Some(min) == max {
                    #name::with_capacity(min)
                } else if min > 0 {
                    #name::with_approximate_capacity(min)
                } else {
                    #name::new_default()
                };

                for item in iter {
                    collection.add(item);
                }
                collection
            }
        }
    };
    gen.into()
}

/// This macro is used to derive the [`IntoIterator`] a standard implementation for all the data
/// structures that implement the [`Collection`] trait. This macro will create a generic wrapper
/// around the data structure and then use some of the [`Collection`] methods to iterate over the
/// elements of the data structure.
///
/// The wrapper will implement the [`Iterator`] and [`ExactSizeIterator`] traits and will be
/// returned by the [`into_iter`] method of the data structure.
///
/// So by implementing this macro, the user can ensure that one of the methods of [`Iterators`] is
/// implemented for the data structure.
///
/// # Panics
/// This macro will panic if the input could not be properly parsed using the [`syn`] crate.
///
/// [`IntoIterator`]: std::iter::IntoIterator
/// [`Iterator`]: std::iter::Iterator
/// [`ExactSizeIterator`]: std::iter::ExactSizeIterator
/// [`into_iter`]: std::iter::IntoIterator::into_iter
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
/// [`Iterators`]: ../trait_based_collection/collection/trait.Iterators.html
#[proc_macro_derive(IntoIterator)]
pub fn into_iterator_collection(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).expect("Could not parse input");

    impl_derive_into_iterator(&ast)
}

/// Internal function that implements the [`IntoIterator`] trait for all the data structures that
/// implement the [`Collection`] trait. This function is used by the crates
/// [`IntoIterator`](crate::IntoIterator) and [`All`](crate::All) macros.
///
/// [`IntoIterator`]: std::iter::IntoIterator
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
fn impl_derive_into_iterator(ast: &DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let iter_struct = format_ident!("{}IntoIter", name);

    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();
    let types = ast.generics.type_params().collect::<Vec<_>>();
    assert!(
        !types.is_empty(),
        "#[derive(IntoIterator)] needs at least one type parameter"
    );
    let ty = &types[0].ident;
    let documentation = format!(
        "Iterator over the elements of a [`{}`]. This struct is \
        created by the [`into_iter`] method on [`{0}`]. See its documentation for more.\n\n\
        [`into_iter`]: Collection::into_iter",
        name
    );

    let gen = quote! {
        #[doc = #documentation]
        pub struct #iter_struct #ty_generics(#name #ty_generics) #where_clause;

        impl #ty_generics Iterator for #iter_struct #ty_generics #where_clause {
            type Item = #ty;

            fn next(&mut self) -> Option<Self::Item> {
                self.0.remove()
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                let size = self.0.len();
                (size, Some(size))
            }
        }

        impl #impl_generics ExactSizeIterator for #iter_struct #ty_generics #where_clause {}

        impl #impl_generics IntoIterator for #name #ty_generics #where_clause {
            type Item = #ty;
            type IntoIter = #iter_struct #ty_generics;

            fn into_iter(self) -> Self::IntoIter {
                #iter_struct(self)
            }
        }
    };
    gen.into()
}

/// This macro is used to derive the [`Default`] a standard implementation for all the data
/// structures that implement the [`Collection`] trait. The default implementation of the data
/// structure will use the [`new_default`] method of the [`Collection`] trait.
///
/// # Panics
/// This macro will panic if the input could not be properly parsed using the [`syn`] crate.
///
/// [`Default`]: std::default::Default
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
/// [`new_default`]: ../trait_based_collection/collection/trait.Collection.html#tymethod.new_default
#[proc_macro_derive(Default)]
pub fn default_collection(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).expect("Could not parse input");

    impl_derive_default(&ast)
}

/// Internal function that implements the [`Default`] trait for all the data structures that
/// implement the [`Collection`] trait. This function is used by the crates
/// [`Default`](crate::Default) and [`All`](crate::All) macros.
///
/// [`Default`]: std::default::Default
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
fn impl_derive_default(ast: &DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    let gen = quote! {
        impl #impl_generics Default for #name #ty_generics #where_clause {
            fn default() -> Self {
                #name::new_default()
            }
        }
    };
    gen.into()
}

/// This macro is used to derive the [`Extend`] trait for all the data structures that implement the
/// [`Collection`] trait. The [`Extend`] trait is implemented by iteratively adding the elements of
/// the iterator to the data structure using the [`add`] method of the [`Collection`] trait.
///
/// # Panics
/// This macro will panic if the input could not be properly parsed using the [`syn`] crate.
///
/// [`Extend`]: std::iter::Extend
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
/// [`add`]: ../trait_based_collection/collection/trait.Collection.html#tymethod.add
#[proc_macro_derive(Extend)]
pub fn extend_collection(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).expect("Could not parse input");

    impl_derive_extend(&ast)
}

/// Internal function that implements the [`Extend`] trait for all the data structures that
/// implement the [`Collection`] trait. This function is used by the crates
/// [`Extend`](crate::Extend) and [`All`](crate::All) macros.
///
/// [`Extend`]: std::iter::Extend
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
fn impl_derive_extend(ast: &DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();
    let types = ast.generics.type_params().collect::<Vec<_>>();
    assert!(
        !types.is_empty(),
        "#[derive(Extend)] needs at least one type parameter"
    );
    let ty = &types[0].ident;

    let gen = quote! {
        impl #impl_generics Extend<#ty> for #name #ty_generics #where_clause {
            fn extend<I: IntoIterator<Item = #ty>>(&mut self, iter: I) {
                for item in iter {
                    self.add(item);
                }
            }
        }
    };
    gen.into()
}

/// This macro is used to derive the [`Display`] trait for all the data structures that implement
/// the [`Collection`] trait. The [`Display`] trait is implemented by iterating over the elements of
/// the data structure using [`iter`] and printing them using the [`Display`] trait of the type of the elements.
///
/// The elements are separated by a comma and enclosed in square brackets.
///
/// # Panics
/// This macro will panic if the input could not be properly parsed using the [`syn`] crate.
///
/// [`Display`]: std::fmt::Display
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
/// [`iter`]: ../trait_based_collection/collection/trait.Collection.html#tymethod.iter
#[proc_macro_derive(Display)]
pub fn display_collection(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).expect("Could not parse input");

    impl_derive_display(&ast)
}

/// Internal function that implements the [`Display`] trait for all the data structures that
/// implement the [`Collection`] trait. This function is used by the crates
/// [`Display`](crate::Display) and [`All`](crate::All) macros.
///
/// [`Display`]: std::fmt::Display
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
fn impl_derive_display(ast: &DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();
    let types = ast.generics.type_params().collect::<Vec<_>>();
    assert!(
        !types.is_empty(),
        "#[derive(Extend)] needs at least one type parameter"
    );
    let ty = &types[0].ident;
    // Adds to where clause that must implement Display for the type
    let where_clause = match where_clause {
        Some(where_clause) => {
            let mut where_clause = where_clause.clone();
            where_clause
                .predicates
                .push(parse_quote!(#ty: std::fmt::Display));
            where_clause
        }
        None => parse_quote!(where #ty: std::fmt::Display),
    };

    let gen = quote! {
        impl #impl_generics std::fmt::Display for #name #ty_generics #where_clause {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, "[")?;
                for (i, item) in self.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", item)?;
                }
                write!(f, "]")
            }
        }
    };
    gen.into()
}

/// Generates a new macro for the [`Collection`] that follows the same syntax as array expressions.
/// The macro will be exported to the crate root and will be named the same as the collection
/// but in snake case.
///
/// # Panics
/// This macro will panic if the input could not be properly parsed using the [`syn`] crate.
///
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
// Generic version of vec!
#[proc_macro_derive(NewMacro)]
pub fn new_macro_collection(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).expect("Could not parse input");

    impl_derive_new_macro(&ast)
}

/// Internal function that generates a new macro for the [`Collection`] that follows the same syntax
/// as array expressions. This function is used by the crates [`NewMacro`](crate::NewMacro) and
/// [`All`](crate::All) macros.
///
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
fn impl_derive_new_macro(ast: &DeriveInput) -> TokenStream {
    let name = &ast.ident;

    let lower_name = format_ident!("{}", name.to_string().to_case(Case::Snake));
    let import = format!(
        "use trait_based_collection::{{prelude::*, {name}, {lower_name}}};",
        name = name,
        lower_name = lower_name
    );
    let documentation = format!(
        "Creates a [`{0}`] containing the arguments.\n\n\
    {1}! allows `{0}`s to be defined with the same syntax as array expressions.\n\
    There are three forms of this macro:\n\n\
    - Create an empty [`{0}`]:\n\n\
    ```\n\
    {2}\n\n\
    let mut c = {1}![];\n\
    c.add(1);\n\
    assert_eq!(c.remove(), Some(1));\n\
    ```\n\n\
    - Create a [`{0}`] containing a given list of elements:\n\n\
    ```\n\
    {2}\n\
    use std::iter::zip;\n\n\
    let c1 = {1}![1, 2, 3];\n\
    let c2 = {0}::from_iter([1, 2, 3].into_iter());\n\
    for (actual, expected) in zip(c1, c2) {{\n    \
        assert_eq!(actual, expected);\n\
    }}\n\
    ```\n\n\
    - Create a [`{0}`] from a given element and size:\n\n\
    ```\n\
    {2}\n\
    use std::iter::zip;\n\n\
    let c1 = {1}![1; 3];\n\
    let c2 = {0}::from_iter([1; 3].into_iter());\n\
    for (actual, expected) in zip(c1, c2) {{\n    \
        assert_eq!(actual, expected);\n\
    }}\n\
    ```\n\n\
    Note that unlike array expressions this syntax supports all elements\n\
    which implement [`Clone`] and the number of elements doesn't have to be\n\
    a constant.\n\n\
    This will use `clone` to duplicate an expression, so one should be careful\n\
    using this with types having a nonstandard `Clone` implementation. For\n\
    example, `{1}![Rc::new(1); 5]` will create a vector of five references\n\
    to the same boxed integer value, not five references pointing to independently\n\
    boxed integers.\n\n\
    [`Clone`]: std::clone::Clone\n\
    [`{0}`]: crate::{0}",
        name, lower_name, import
    );

    let new_macro = quote! {
        #[doc = #documentation]
        #[macro_export]
        macro_rules! #lower_name {
            () => {
                #name::default()
            };
            ($($elem:expr),*) => {
                {
                    #name::from_iter([$($elem),*].into_iter())
                    /* TODO: Find macro that calculates the capacity of the collection
                    let mut collection = #name::with_capacity(size!($($elem),*));
                    $(collection.add($elem);)*
                    collection */
                }
            };
            ($elem:expr; $n:expr) => (
                {
                    let mut collection = #name::with_capacity($n);
                    for _ in 0..$n {
                        collection.add($elem.clone());
                    }
                    collection
                }
            );
        }
    };
    new_macro.into()
}

/// This macro is used to derive the [`Drop`] trait for all the data structures that implement the
/// [`Collection`] trait. The drop implementation will call the [`clear`] method of the collection.
/// This will remove all the elements from the collection ensuring that the elements are also
/// dropped.
///
/// # Panics
/// This macro will panic if the input could not be properly parsed using the [`syn`] crate.
///
/// [`Drop`]: std::ops::Drop
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
/// [`clear`]: ../trait_based_collection/collection/trait.Collection.html#tymethod.clear
#[proc_macro_derive(Drop)]
pub fn drop_collection(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).expect("Could not parse input");

    impl_derive_drop(&ast)
}

/// Internal function that generates the [`Drop`] trait for all the data structures that implement
/// the [`Collection`] trait. This function is used by the crates [`Drop`](crate::Drop) and
/// [`All`](crate::All) macros.
///
/// [`Drop`]: std::ops::Drop
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
fn impl_derive_drop(ast: &DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    let gen = quote! {
        impl #impl_generics Drop for #name #ty_generics #where_clause {
            fn drop(&mut self) {
                self.clear();
            }
        }
    };
    gen.into()
}

/// This macro is used to derive the [`Index`] and [`IndexMut`] traits for all the data structures
/// that implement the [`Collection`] trait. Both traits will use the [`get`] and [`get_mut`]
/// methods of the collection to access the elements and will panic if the index is out of bounds.
///
/// # Panics
/// This macro will panic if the input could not be properly parsed using the [`syn`] crate.
///
/// [`Index`]: std::ops::Index
/// [`IndexMut`]: std::ops::IndexMut
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
/// [`get`]: ../trait_based_collection/collection/trait.Collection.html#tymethod.get
/// [`get_mut`]: ../trait_based_collection/collection/trait.Collection.html#tymethod.get_mut
#[proc_macro_derive(Index)]
pub fn index_collection(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).expect("Could not parse input");

    impl_derive_index(&ast)
}

/// Internal function that generates the [`Index`] and [`IndexMut`] traits for all the data
/// structures that implement the [`Collection`] trait. This function is used by the crates
/// [`Index`](crate::Index) and [`All`](crate::All) macros.
///
/// [`Index`]: std::ops::Index
/// [`IndexMut`]: std::ops::IndexMut
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
fn impl_derive_index(ast: &DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();
    let types = ast.generics.type_params().collect::<Vec<_>>();
    assert!(
        !types.is_empty(),
        "#[derive(Index)] needs at least one type parameter"
    );
    let ty = &types[0].ident;

    let gen = quote! {
        impl #impl_generics std::ops::Index<usize> for #name #ty_generics #where_clause {
            type Output = #ty;

            fn index(&self, index: usize) -> &Self::Output {
                let len = self.len();
                self.get(index).expect(format!("Index out of bounds: the len is {} but the index is {}", len, index).as_str())
            }
        }

        impl #impl_generics std::ops::IndexMut<usize> for #name #ty_generics #where_clause {
            fn index_mut(&mut self, index: usize) -> &mut Self::Output {
                let len = self.len();
                self.get_mut(index).expect(format!("Index out of bounds: the len is {} but the index is {}", len, index).as_str())
            }
        }
    };
    gen.into()
}
/// This macro encapsulates all the Derive macros for a [`Collection`]. Currently it derives the
/// following traits:
/// - [`FromIterator`](crate::FromIterator)
/// - [`IntoIterator`](crate::IntoIterator)
/// - [`Default`](crate::Default)
/// - [`Extend`](crate::Extend)
/// - [`Display`](crate::Display)
/// - [`NewMacro`](crate::NewMacro)
/// - [`Drop`](crate::Drop)
/// - [`Index`](crate::Index)
///
/// # Panics
/// This macro will panic if the input could not be properly parsed using the [`syn`] crate.
///
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
#[proc_macro_derive(All)]
pub fn all_collection(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).expect("Could not parse input");

    let from_iterator: TokenStream2 = impl_derive_from_iterator(&ast).into();
    let into_iterator: TokenStream2 = impl_derive_into_iterator(&ast).into();
    let default: TokenStream2 = impl_derive_default(&ast).into();
    let extend: TokenStream2 = impl_derive_extend(&ast).into();
    let display: TokenStream2 = impl_derive_display(&ast).into();
    let new_macro: TokenStream2 = impl_derive_new_macro(&ast).into();
    let drop: TokenStream2 = impl_derive_drop(&ast).into();
    let index: TokenStream2 = impl_derive_index(&ast).into();

    let combined = quote! {
        #from_iterator
        #into_iterator
        #default
        #extend
        #display
        #new_macro
        #drop
        #index
    };
    combined.into()
}


/// A struct that stores the arguments for the [`test_collection`] macro. It stores both the data
/// structures that are being tested and extra macros that are being applied to the test.
///
/// This struct implements the `Parse` trait, which is used by the `syn` crate to parse the
/// arguments into a struct.
///
/// # Example
/// ```
/// use trait_based_collection_macros::test_collection;
/// use trait_based_collection::*;
///
/// #[test_collection(Stack, ArrayStack; should_panic)]
/// fn test<C: Collection<usize>>(mut stack: C) {
///    stack[1000]; // This should panic
/// }
/// ```
///
/// [`test_collection`]: macro@test_collection
struct TestArgs {
    /// Names of the data structures that are being tested.
    collection_names: HashSet<Ident>,
    /// Extra macros that are being applied to the test.
    macros: HashSet<Ident>,
}

impl Parse for TestArgs {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut collection_names = HashSet::new();
        let mut macros = HashSet::new();

        'set: for (i, set) in [&mut collection_names, &mut macros].into_iter().enumerate() {
            while !input.is_empty() {
                let ident = input.parse::<Ident>()?;
                if set.contains(&ident) {
                    return Err(syn::Error::new(
                        ident.span(),
                        format!("{} is already in the set {}", ident, i),
                    ));
                }
                set.insert(ident);
                if input.is_empty() {
                    break 'set;
                }
                if input.peek(Token![;]) {
                    input.parse::<Token![;]>()?;
                    continue 'set;
                }
                input.parse::<Token![,]>()?;
            }
        }

        Ok(Self { collection_names, macros })
    }
}

/// A macro that duplicates a test for multiple data structures. This macros has the following
/// functionalities:
///
/// - Any number of data structures can be tested.
/// - Any number of extra macros can be applied to the test.
/// - The test takes a single argument, which for the test will be properly initialized with the
/// a data structure of the type that is being tested.
/// - The type of the argument is automatically changed to the data structure that is being tested.
///
/// # Panics
/// The test function must have a single type parameter with a trait bound.
///
/// # Example
/// ```
/// use trait_based_collection_macros::test_collection;
/// use trait_based_collection::*;
///
/// #[test_collection(Stack, ArrayStack; should_panic)]
/// fn test<C: Collection<usize>>(mut stack: C) {
///    stack[1000]; // This should panic
/// }
/// ```
#[proc_macro_attribute]
pub fn test_collection(args: TokenStream, input: TokenStream) -> TokenStream {
    let args = syn::parse_macro_input!(args as TestArgs);
    let mut input = syn::parse_macro_input!(input as ItemFn);

    impl_test_collection(&args, &mut input)
}

/// Recursively modifies a token tree to replace the type parameter with the data structure that is
/// being tested. This avoids the need to write the same test for test related to class methods.
fn modify_token_tree(tree: TokenTree, collection_name: &Ident, ty: &Ident) -> TokenTree {
    match tree {
        TokenTree::Group(group) => TokenTree::Group(Group::new(
            group.delimiter(),
            group
                .stream()
                .into_iter()
                .map(|tree| modify_token_tree(tree, collection_name, ty))
                .collect(),
        )),
        TokenTree::Ident(id) => TokenTree::Ident(if id == *ty {
            collection_name.clone()
        } else {
            id
        }),
        other => other,
    }
}

/// Internal function that generates the functionality of the [`test_collection`] macro. This
/// function is used in all the tests of the main crate.
///
/// # Panics
/// The test function must have a single type parameter with a trait bound.
///
/// [`test_collection`]: macro@crate::test_collection
fn impl_test_collection(args: &TestArgs, input: &mut ItemFn) -> TokenStream {
    let function_name = &input.sig.ident;

    let mut types = input.sig.generics.type_params().collect::<Vec<_>>();
    assert!(
        !types.is_empty(),
        "#[test_collection] needs at least one type parameter"
    );
    let ty = types[0].ident.clone();
    let bound = match types.pop().expect("At least one type parameter is needed").bounds[0] {
        syn::TypeParamBound::Lifetime(_) => panic!("#[test_collection] needs a trait bound"),
        syn::TypeParamBound::Trait(ref bound) => (bound.path.segments[0].arguments.clone()),
    };
    input.sig.generics = syn::parse_quote! {};

    assert_eq!(input.sig.inputs.len(), 1, "#[test_collection] needs one argument");
    let input_ = match input.sig.inputs[0] {
        FnArg::Receiver(_) => panic!("#[test_collection] needs a parameter"),
        FnArg::Typed(ref input) => match *input.pat {
            Pat::Ident(ref input) => input.clone(),
            _ => panic!("#[test_collection] needs a parameter"),
        },
    };
    let input_id = &input_.ident;
    let mut_ = input_.mutability;

    let tests = args
        .collection_names
        .iter()
        .map(|collection_name| {
            let name = format_ident!(
                "{}_{}",
                function_name,
                collection_name.to_string().to_case(Case::Snake)
            );
            let macros = args.macros.iter().fold(quote!(#[test]), |acc, macro_name| {
                quote! {
                    #acc
                    #[#macro_name]
                }
            });
            let block: TokenStream2 = input
                .block
                .clone()
                .into_token_stream()
                .into_iter()
                .map(|t| modify_token_tree(t, collection_name, &ty))
                .collect();

            quote! {
                #macros
                fn #name() {
                    let #mut_ #input_id: #collection_name #bound = #collection_name::new_default();
                    #block
                }
            }
        })
        .fold(quote! {}, |acc, new| {
            quote! {
                #acc
                #new
            }
        });

    tests.into()
}

/// This macro is used to check if the collection is expanded when it is full. This is used to
/// ensure that the collection is expanded when it is full. This macro should be used in the
/// implementation of the [`add`] method of the [`Collection`] trait if the collection also implements
/// [`FixedSizeCollection`].
///
/// This version of the macro is used for collections that are not public. If the collection is
/// public, use the [`check_expansion_add`] macro instead.
///
/// # Panics
/// If any argument is passed to the macro.
///
/// [`check_expansion_add`]: macro@check_expansion_add
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
/// [`FixedSizeCollection`]: ../trait_based_collection/collection/trait.FixedSizeCollection.html
/// [`add`]: ../trait_based_collection/collection/trait.Collection.html#tymethod.add
#[proc_macro_attribute]
pub fn internal_check_expansion_add(args: TokenStream, input: TokenStream) -> TokenStream {
    assert!(
        syn::parse_macro_input!(args as TestArgs).collection_names.is_empty(),
        "internal_check_expansion does not support arguments"
    );

    let input = syn::parse_macro_input!(input as ItemFn);
    impl_internal_check_expansion_add(&input)
}

/// Internal function that generates the functionality of the [`internal_check_expansion_add`]
/// macro. This function is used in all the [`add`] methods of the main crate that also implement
/// [`FixedSizeCollection`].
///
/// [`internal_check_expansion_add`]: macro@crate::internal_check_expansion_add
/// [`FixedSizeCollection`]: ../trait_based_collection/collection/trait.FixedSizeCollection.html
/// [`add`]: ../trait_based_collection/collection/trait.Collection.html#tymethod.add
fn impl_internal_check_expansion_add(input: &ItemFn) -> TokenStream {
    let signature = &input.sig;
    let content = &input.block;

    let gen = quote! {
        #signature {
            if crate::collection::check_expansion(self) {
                return;
            }
            #content
        }
    };
    gen.into()
}

/// This macro is used to check if the collection is expanded when it is full. This is used to
/// ensure that the collection is expanded when it is full. This macro should be used in the
/// implementation of the [`add`] method of the [`Collection`] trait if the collection also implements
/// [`FixedSizeCollection`].
///
/// # Panics
/// If any argument is passed to the macro.
///
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
/// [`FixedSizeCollection`]: ../trait_based_collection/collection/trait.FixedSizeCollection.html
/// [`add`]: ../trait_based_collection/collection/trait.Collection.html#tymethod.add
#[proc_macro_attribute]
pub fn check_expansion_add(args: TokenStream, input: TokenStream) -> TokenStream {
    assert!(
        syn::parse_macro_input!(args as TestArgs).collection_names.is_empty(),
        "internal_check_expansion does not support arguments"
    );

    let input = syn::parse_macro_input!(input as ItemFn);

    impl_check_expansion_add(&input)
}

/// Internal function that generates the functionality of the [`check_expansion_add`] macro. This
/// function is used in all the [`add`] methods of the main crate that also implement
/// [`FixedSizeCollection`].
///
/// [`check_expansion_add`]: macro@crate::check_expansion_add
/// [`FixedSizeCollection`]: ../trait_based_collection/collection/trait.FixedSizeCollection.html
/// [`add`]: ../trait_based_collection/collection/trait.Collection.html#tymethod.add
fn impl_check_expansion_add(input: &ItemFn) -> TokenStream {
    let signature = &input.sig;
    let content = &input.block;

    let gen = quote! {
        #signature {
            if trait_based_collection::collection::check_expansion(self) {
                return;
            }
            #content
        }
    };
    gen.into()
}

/// Struct that is used to parse the arguments for the [`iterator`] macro.
///
/// [`iterator`]: macro@crate::iterator
struct IteratorArgs {
    /// The name of the data structure that is used to store the elements of the collection.
    collection_name: Ident,
    /// The name of iterator that is generated.
    iterator_name: Ident,
    /// Whether the iterator is a reference iterator.
    is_ref: bool,
    /// Code executed to get the next element of the iterator.
    content: Block,
}

impl Parse for IteratorArgs {
    fn parse(input: ParseStream) -> Result<Self> {
        let collection_name = input.parse::<Ident>()?;
        input.parse::<Token![,]>()?;
        let iterator_name = input.parse::<Ident>()?;
        input.parse::<Token![,]>()?;
        let is_ref = input.peek(Token![ref]);
        if is_ref {
            input.parse::<Token![ref]>()?;
        } else {
            input.parse::<Token![mut]>()?;
        }
        input.parse::<Token![,]>()?;
        let content = input.parse::<Block>()?;

        Ok(Self {
            collection_name,
            iterator_name,
            is_ref,
            content,
        })
    }
}

/// This macro is used to generate the implementation of the [`Iterator`], reference
/// [`IntoIterator`], and [`ExactSizeIterator`] traits for a [`Collection`]. This macro can be used
/// to avoid the boilerplate code that is required to implement these traits. This macro can
/// generate the implementation for both mutable and immutable references.
///
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
/// [`FixedSizeCollection`]: ../trait_based_collection/collection/trait.FixedSizeCollection.html
/// [`Iterator`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html
#[proc_macro]
pub fn iterator(input: TokenStream) -> TokenStream {
    let iterator = syn::parse_macro_input!(input as IteratorArgs);
    impl_iterator(&iterator)
}

/// Internal function that generates the functionality of the [`iterator`] macro. This function is
/// used in all the [`Collection`] implementations of the main crate.
///
/// [`iterator`]: macro@crate::iterator
/// [`Collection`]: ../trait_based_collection/collection/trait.Collection.html
/// [`FixedSizeCollection`]: ../trait_based_collection/collection/trait.FixedSizeCollection.html
fn impl_iterator(iterator: &IteratorArgs) -> TokenStream {
    let collection_name = &iterator.collection_name;
    let iterator_name = &iterator.iterator_name;
    let is_ref = iterator.is_ref;
    let content = &iterator.content;

    let ref_type = if is_ref { quote!(&'a) } else { quote!(&'a mut) };

    let gen = quote! {
        impl<'a, T> Iterator for #iterator_name<'a, T> {
            type Item = #ref_type T;

            fn next(&mut self) -> Option<Self::Item>
            #content

            fn size_hint(&self) -> (usize, Option<usize>) {
                (self.len, Some(self.len))
            }
        }

        impl<'a, T> ExactSizeIterator for #iterator_name<'a, T> {}

        impl<'a, T> IntoIterator for #ref_type #collection_name<T> {
            type Item = #ref_type T;
            type IntoIter = #iterator_name<'a, T>;

            fn into_iter(self) -> Self::IntoIter {
                #iterator_name::new(self)
            }
        }
    };
    gen.into()
}
