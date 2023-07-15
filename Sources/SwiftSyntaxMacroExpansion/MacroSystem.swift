//===----------------------------------------------------------------------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2023 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

import SwiftDiagnostics
import SwiftSyntax
@_spi(MacroExpansion) import SwiftParser
@_spi(MacroExpansion) import SwiftSyntaxMacros

/// Check if a 'DeclSyntax', 'StmtSyntax', or 'ExprSyntax' is at top level.
private func isTopLevel(node: some SyntaxProtocol) -> Bool {
  return true == node
    .parent? /* CodeBlockItem */
    .parent? /* CodeBlockItemList */
    .is(SourceFileSyntax.self).self
}

private func expandFreestandingMemberDeclList(
  definition: Macro.Type,
  node: some FreestandingMacroExpansionSyntax
) throws -> MemberDeclListSyntax? {
  guard let expanded = try expandFreestandingMacroAdjusted(
    definition: definition,
    macroRole: inferFreestandingMacroRole(definition: definition),
    node: node
  ) else {
    return nil
  }

  return Parser.parseExpandedMemberDeclList(
    source: "\n\n" + expanded
  )
}

private func expandFreestandingCodeItemList(
  definition: Macro.Type,
  node: some FreestandingMacroExpansionSyntax
) throws -> CodeBlockItemListSyntax? {
  guard let expanded = try expandFreestandingMacroAdjusted(
    definition: definition,
    macroRole: inferFreestandingMacroRole(definition: definition),
    node: node
  ) else {
    return nil
  }

  return Parser.parseExpandedCodeBlockItemList(
    source: "\n\n" + expanded,
    isAtTopLevel: isTopLevel(node: node)
  )
}

private func expandFreestandingExpr(
  definition: Macro.Type,
  node: some FreestandingMacroExpansionSyntax
) throws -> ExprSyntax? {
  guard let expanded = try expandFreestandingMacroAdjusted(
    definition: definition,
    macroRole: .expression,
    node: node
  ) else {
    return nil
  }
  return "\(raw: expanded)"
}

private func expandFreestandingMacroAdjusted(
  definition: Macro.Type,
  macroRole: MacroRole,
  node: some FreestandingMacroExpansionSyntax
) throws -> String? {

  guard var expanded = expandFreestandingMacro(
    definition: definition,
    macroRole: macroRole,
    node: node,
    in: BasicMacroExpansionContext()
  ) else {
    return nil
  }
  let indentation = node.baseIndentation
  return expanded.applying(indentation: indentation)
}

private func expandMemberMacro(
  definition: MemberMacro.Type,
  attributeNode: AttributeSyntax,
  attachedTo: DeclSyntax
) throws -> MemberDeclListSyntax? {
  let context = BasicMacroExpansionContext()
  guard var expanded = expandAttachedMacro(
    definition: definition,
    macroRole: .member,
    attributeNode: attributeNode,
    declarationNode: attachedTo,
    parentDeclNode: nil,
    extendedType: nil,
    conformanceList: nil,
    in: context
  ) else {
    return nil
  }
  expanded = "\n\n" + expanded.applying(indentation: attachedTo.baseIndentation)
  return Parser.parseExpandedMemberDeclList(source: expanded)
}

private func expandMemberAttributeMacro(
  definition: MemberAttributeMacro.Type,
  attributeNode: AttributeSyntax,
  attachedTo declaration: DeclSyntax,
  providingAttributeFor member: DeclSyntax
) throws -> AttributeListSyntax? {
  let context = BasicMacroExpansionContext()
  guard var expanded = expandAttachedMacro(
    definition: definition,
    macroRole: .memberAttribute,
    attributeNode: attributeNode,
    declarationNode: member,
    parentDeclNode: declaration,
    extendedType: nil,
    conformanceList: nil,
    in: context
  ) else {
    return nil
  }
  expanded = "\n" + expanded.applying(indentation: member.baseIndentation)
  return Parser.parseExpandedAttributeList(source: expanded)
}

private func expandPeerMacroMember(
  definition: PeerMacro.Type,
  attributeNode: AttributeSyntax,
  attachedTo: DeclSyntax
) throws -> MemberDeclListSyntax? {
  let context = BasicMacroExpansionContext()
  guard var expanded = expandAttachedMacro(
    definition: definition,
    macroRole: .peer,
    attributeNode: attributeNode,
    declarationNode: attachedTo,
    parentDeclNode: nil,
    extendedType: nil,
    conformanceList: nil,
    in: context
  ) else {
    return nil
  }
  expanded = "\n\n" + expanded.applying(indentation: attachedTo.baseIndentation)
  return Parser.parseExpandedMemberDeclList(source: expanded)
}

private func expandPeerMacroCodeItem(
  definition: PeerMacro.Type,
  attributeNode: AttributeSyntax,
  attachedTo: DeclSyntax
) throws -> CodeBlockItemListSyntax? {
  let context = BasicMacroExpansionContext()
  guard var expanded = expandAttachedMacro(
    definition: definition,
    macroRole: .peer,
    attributeNode: attributeNode,
    declarationNode: attachedTo,
    parentDeclNode: nil,
    extendedType: nil,
    conformanceList: nil,
    in: context
  ) else {
    return nil
  }
  expanded = "\n\n" + expanded.applying(indentation: attachedTo.baseIndentation)
  return Parser.parseExpandedCodeBlockItemList(source: expanded, isAtTopLevel: isTopLevel(node: attachedTo))
}

private func expandAccessorMacroWithBlock(
  definition: AccessorMacro.Type,
  attributeNode: AttributeSyntax,
  attachedTo: DeclSyntax
) throws -> AccessorBlockSyntax? {
  let context = BasicMacroExpansionContext()
  guard var expanded = expandAttachedMacro(
    definition: definition,
    macroRole: .accessor,
    attributeNode: attributeNode,
    declarationNode: attachedTo,
    parentDeclNode: nil,
    extendedType: nil,
    conformanceList: nil,
    in: context
  ) else {
    return nil
  }
  expanded = "\n" + expanded.applying(indentation: attachedTo.baseIndentation)
  return Parser.parseExpandedAccessorBlock(source: expanded)
}

private func expandAccessorMacroWithoutBlock(
  definition: AccessorMacro.Type,
  attributeNode: AttributeSyntax,
  attachedTo: DeclSyntax
) throws -> AccessorListSyntax? {
  let context = BasicMacroExpansionContext()
  guard var expanded = expandAttachedMacro(
    definition: definition,
    macroRole: .accessor,
    attributeNode: attributeNode,
    declarationNode: attachedTo,
    parentDeclNode: nil,
    extendedType: nil,
    conformanceList: nil,
    in: context
  ) else {
    return nil
  }
  expanded = "\n\n" + expanded.applying(indentation: attachedTo.baseIndentation)
  return Parser.parseExpandedAccessorList(source: expanded)
}

private func expandExtensionMacro(
  definition: MemberMacro.Type,
  attributeNode: AttributeSyntax,
  attachedTo: DeclSyntax
) throws -> CodeBlockItemListSyntax? {
  let extendedType: TypeSyntax
  if let identified = attachedTo.asProtocol(IdentifiedDeclSyntax.self) {
    extendedType = "\(identified.identifier.trimmed)"
  } else if let ext = attachedTo.as(ExtensionDeclSyntax.self) {
    extendedType = "\(ext.extendedType.trimmed)"
  } else {
    return nil
  }

  let context = BasicMacroExpansionContext()
  guard var expanded = expandAttachedMacro(
    definition: definition,
    macroRole: .extension,
    attributeNode: attributeNode,
    declarationNode: attachedTo,
    parentDeclNode: nil,
    extendedType: extendedType,
    conformanceList: [],
    in: context
  ) else {
    return nil
  }
  expanded = "\n\n" + expanded
  return Parser.parseExpandedCodeBlockItemList(source: expanded, isAtTopLevel: true)
}

/// Describes the kinds of errors that can occur within a macro system.
enum MacroSystemError: Error {
  /// Indicates that a macro with the given name has already been defined.
  case alreadyDefined(new: Macro.Type, existing: Macro.Type)

  /// Indicates that an unknown macro was encountered during expansion.
  case unknownMacro(name: String, node: Syntax)

  /// Indicates that a macro evaluated as an expression by the given node
  /// is not an expression macro.
  case requiresExpressionMacro(macro: Macro.Type, node: Syntax)

  /// Indicates that a macro evaluated as a code item by the given node
  /// is not suitable for code items.
  case requiresCodeItemMacro(macro: Macro.Type, node: Syntax)

  /// Indicates that a macro produced diagnostics during evaluation. The
  /// diagnostics might not specifically include errors, but will be reported
  /// nonetheless.
  case evaluationDiagnostics(node: Syntax, diagnostics: [Diagnostic])
}

/// A system of known macros that can be expanded syntactically
struct MacroSystem {
  var macros: [String: Macro.Type] = [:]

  /// Create an empty macro system.
  init() {}

  /// Add a macro to the system.
  ///
  /// Throws an error if there is already a macro with this name.
  mutating func add(_ macro: Macro.Type, name: String) throws {
    if let knownMacro = macros[name] {
      throw MacroSystemError.alreadyDefined(new: macro, existing: knownMacro)
    }

    macros[name] = macro
  }

  /// Look for a macro with the given name.
  func lookup(_ macroName: String) -> Macro.Type? {
    return macros[macroName]
  }
}

/// Syntax rewriter that evaluates any macros encountered along the way.
class MacroApplication<Context: MacroExpansionContext>: SyntaxRewriter {
  let macroSystem: MacroSystem
  var context: Context
  var skipNodes: Set<Syntax> = []

  /// Store expanded extension while visiting member decls. This should be
  /// added to top-level 'CodeBlockItemList'.
  var extensions: [CodeBlockItemSyntax]?

  init(
    macroSystem: MacroSystem,
    context: Context
  ) {
    self.macroSystem = macroSystem
    self.context = context
    super.init(viewMode: .sourceAccurate)
  }

  override func visitAny(_ node: Syntax) -> Syntax? {
    if skipNodes.contains(node) {
      return nil
    }

    // Expand 'MacroExpansionExpr'.
    // Note that 'MacroExpansionExpr'/'MacroExpansionExprDecl' at code item
    // position are handled by 'visit(_:CodeBlockItemListSyntax)'. Here's only
    // expression inside other syntax node.
    if let expanded = expandExpr(node: node) {
      return Syntax(visit(expanded))
    }

    if let declSyntax = node.as(DeclSyntax.self),
      let attributedNode = node.asProtocol(WithAttributesSyntax.self),
      let attributes = attributedNode.attributes
    {
      // Visit the node.
      skipNodes.insert(node)
      let visitedNode = self.visit(declSyntax).asProtocol(WithAttributesSyntax.self)!
      skipNodes.remove(node)

      // Remove any attached attributes.
      let newAttributes = attributes.filter {
        guard case let .attribute(attribute) = $0 else {
          return true
        }

        guard let attributeName = attribute.attributeName.as(SimpleTypeIdentifierSyntax.self)?.name.text,
          let macro = macroSystem.macros[attributeName]
        else {
          return true
        }

        return !(macro is AttachedMacro.Type)
      }

      if newAttributes.isEmpty {
        return Syntax(fromProtocol: visitedNode.with(\.attributes, nil))
      }

      return Syntax(fromProtocol: visitedNode.with(\.attributes, AttributeListSyntax(newAttributes)))
    }

    return nil
  }

  override func visit(_ node: CodeBlockItemListSyntax) -> CodeBlockItemListSyntax {
    let isAtTopLevel = node.parent?.is(SourceFileSyntax.self) == true

    var newItems: [CodeBlockItemSyntax] = []
    for item in node {
      if let expanded = expandCodeBlockItem(node: item) {
        for item in expanded {
          newItems.append(visit(item))
        }
        continue
      }

      // Recurse on the child node.
      let newItem = visit(item.item)
      newItems.append(item.with(\.item, newItem))

      // Expand any peer declarations or conformances triggered by macros used
      // as attributes.
      if case let .decl(decl) = item.item {
        for item in expandPeers(ofCodeBlockItemDecl: decl) {
          newItems.append(visit(item))
        }
      }
    }

    if isAtTopLevel, let extensions {
      newItems.append(contentsOf: extensions)
    }

    return CodeBlockItemListSyntax(newItems)
  }

  override func visit(_ node: MemberDeclListSyntax) -> MemberDeclListSyntax {
    let parentDeclGroup = node.parent?.as(DeclSyntax.self)
    var newItems: [MemberDeclListItemSyntax] = []

    for var item in node {
      // Expand freestanding macro.
      if let expanded = expandMemberDecl(node: item) {
        for item in expanded {
          newItems.append(visit(item))
        }
        continue
      }

      // Expand member attribute members attached to the declaration context.
      // Note that MemberAttribute macros are _not_ applied to generated members
      if let parentDeclGroup, item.decl is WithAttributesSyntax {
        var newAttributes = expandAttributes(of: item.decl, parentDecl: parentDeclGroup).map {
          visit($0)
        }
        if !newAttributes.isEmpty {
          let decl = item.decl as! WithAttributesSyntax
          if let existingAttrs = decl.attributes {
            newAttributes.insert(contentsOf: existingAttrs, at: 0)
          }
          item.decl = decl.with(\.attributes, AttributeListSyntax(newAttributes)).cast(DeclSyntax.self)
        }
      }

      // Recurse on the child node.
      newItems.append(visit(item))

      // Expand any peer macro on this member.
      for peer in expandPeers(ofMemberDecl: item.decl) {
        newItems.append(visit(peer))
      }
    }

    // Expand any member macros of parent.
    if let parentDeclGroup {
      for member in expandMembers(of: parentDeclGroup) {
        newItems.append(visit(member))
      }
    }

    return .init(newItems)
  }

  // Properties
  override func visit(_ node: VariableDeclSyntax) -> DeclSyntax {
    let visitedNode = super.visit(node)
    guard let visitedVarDecl = visitedNode.as(VariableDeclSyntax.self) else {
      return visitedNode
    }

    guard let binding = visitedVarDecl.bindings.first,
      visitedVarDecl.bindings.count == 1
    else {
      return DeclSyntax(node)
    }

    var accessors: [AccessorDeclSyntax] = expandAccessors(of: DeclSyntax(node))
    if accessors.isEmpty {
      return visitedNode
    }

    return DeclSyntax(
      visitedVarDecl.with(
        \.bindings,
        visitedVarDecl.bindings.with(
          \.[visitedVarDecl.bindings.startIndex],
          binding.with(
            \.accessor,
            .accessors(
              .init(
                leftBrace: .leftBraceToken(leadingTrivia: .space),
                accessors: .init(accessors),
                rightBrace: .rightBraceToken(leadingTrivia: .newline)
              )
            )
          )
        )
      )
    )
  }

  // Subscripts
}

/// Attached macro expansions.
extension MacroApplication {
  /// Get pairs of a macro attribute and the macro definition attached to 'decl'
  /// matching 'ofType' macro type. The macros must be registered to
  /// 'macroSystem'.
  /// E.g.
  private func getMacroAttributes<MacroType>(
    attachedTo decl: DeclSyntax,
    ofType: MacroType.Type
  ) -> [(attributeNode: AttributeSyntax, definition: MacroType)] {
    guard let attributedNode = decl.asProtocol(WithAttributesSyntax.self),
          let attributes = attributedNode.attributes
    else {
      return []
    }

    return attributes.compactMap {
      guard case let .attribute(attribute) = $0,
        let attributeName = attribute.attributeName.as(SimpleTypeIdentifierSyntax.self)?.name.text,
        let macro = macroSystem.lookup(attributeName),
        let macroType = macro as? MacroType
      else {
        return nil
      }

      return (attribute, macroType)
    }
  }

  // If any of the custom attributes associated with the given declaration
  // refer to "peer" declaration macros, expand them and return the resulting
  // set of peer declarations.
  private func expandPeers(ofMemberDecl decl: DeclSyntax) -> [MemberDeclListItemSyntax] {
    var peers: [MemberDeclListItemSyntax] = []

    for peerMacro in getMacroAttributes(attachedTo: decl, ofType: PeerMacro.Type.self) {
      do {
        if let expanded = try expandPeerMacroMember(
          definition: peerMacro.definition,
          attributeNode: peerMacro.attributeNode,
          attachedTo: decl
        ) {
          peers.append(contentsOf: expanded)
        }
      } catch {
        context.addDiagnostics(from: error, node: peerMacro.0)
      }
    }
    return peers
  }

  private func expandPeers(ofCodeBlockItemDecl decl: DeclSyntax) -> [CodeBlockItemSyntax] {
    var peers: [CodeBlockItemSyntax] = []

    for peerMacro in getMacroAttributes(attachedTo: decl, ofType: PeerMacro.Type.self) {
      do {
        if let expanded = try expandPeerMacroCodeItem(
          definition: peerMacro.definition,
          attributeNode: peerMacro.attributeNode,
          attachedTo: decl
        ) {
          peers.append(contentsOf: expanded)
        }
      } catch {
        context.addDiagnostics(from: error, node: peerMacro.0)
      }
    }
    return peers
  }

  private func expandMembers(of parentDeclGroup: DeclSyntax) -> [MemberDeclListItemSyntax] {
    var members: [MemberDeclListItemSyntax] = []
    for memberMacro in getMacroAttributes(
      attachedTo: parentDeclGroup,
      ofType: MemberMacro.Type.self
    ) {
      do {
        if let expanded = try expandMemberMacro(
          definition: memberMacro.definition,
          attributeNode: memberMacro.attributeNode,
          attachedTo: parentDeclGroup
        ) {
          members.append(contentsOf: expanded)
        }
      } catch {
        context.addDiagnostics(from: error, node: memberMacro.attributeNode)
      }
    }
    return members
  }

  private func expandAttributes(of decl: DeclSyntax, parentDecl: DeclSyntax) -> [AttributeListSyntax.Element] {

    var attributes: [AttributeListSyntax.Element] = []
    for memberAttributeMacro in getMacroAttributes(
      attachedTo: parentDecl,
      ofType: MemberAttributeMacro.Type.self
    ) {
      do {
        if let expanded = try expandMemberAttributeMacro(
          definition: memberAttributeMacro.definition,
          attributeNode: memberAttributeMacro.attributeNode,
          attachedTo: parentDecl,
          providingAttributeFor: decl
        ) {
          attributes.append(contentsOf: expanded)
        }
      } catch {
        context.addDiagnostics(from: error, node: memberAttributeMacro.attributeNode)
      }
    }
    return attributes
  }

  private func expandAccessors(of decl: DeclSyntax) -> [AccessorDeclSyntax] {
    var accessors: [AccessorDeclSyntax] = []
    for memberAttributeMacro in getMacroAttributes(
      attachedTo: decl,
      ofType: AccessorMacro.Type.self
    ) {
      do {
        if let expanded = try expandAccessorMacroWithoutBlock(
          definition: memberAttributeMacro.definition,
          attributeNode: memberAttributeMacro.attributeNode,
          attachedTo: decl
        ) {
          accessors.append(contentsOf: expanded)
        }
      } catch {
        context.addDiagnostics(from: error, node: memberAttributeMacro.attributeNode)
      }
    }
    return accessors
  }
}

/// Freestanding macro expansion.
extension MacroApplication {
  /// Expand a freestanding macro expansion syntax in a code block item position.
  /// E.g.
  ///   function test() {
  ///     #foo
  ///   }
  func expandCodeBlockItem(node: CodeBlockItemSyntax) -> CodeBlockItemListSyntax? {
    guard let expansion = node.item.asProtocol(FreestandingMacroExpansionSyntax.self),
      let macro = macroSystem.lookup(expansion.macro.text)
    else {
      return nil
    }
    do {
      return try expandFreestandingCodeItemList(definition: macro, node: expansion)
    } catch {
      context.addDiagnostics(from: error, node: expansion)
      return nil
    }
  }

  /// Expand a freestanding macro expansion syntax in a member decl position.
  /// E.g.
  ///   struct S {
  ///     #foo
  ///   }
  func expandMemberDecl(node: MemberDeclListItemSyntax) -> MemberDeclListSyntax? {
    // Expand declaration macros, which produce zero or more declarations.
    guard let declExpansion = node.decl.as(MacroExpansionDeclSyntax.self),
          let macro = macroSystem.macros[declExpansion.macro.text] as? DeclarationMacro.Type else {
      return nil
    }
    do {
      return try expandFreestandingMemberDeclList(definition: macro, node: declExpansion)
    } catch {
      context.addDiagnostics(from: error, node: declExpansion)
      return nil
    }
  }

  /// Expand a freestanding macro expansion in a expression position inside
  /// other products. e.g.
  ///   let a = #foo
  func expandExpr(node: Syntax) -> ExprSyntax? {
    guard let expansion = node.as(MacroExpansionExprSyntax.self),
       let macro = macroSystem.lookup(expansion.macro.text)
    else {
      return nil
    }
    do {
      return try expandFreestandingExpr(definition: macro, node: expansion)
    } catch {
      context.addDiagnostics(from: error, node: node)
      return nil
    }
  }
}

extension DeclSyntax {
  /// Returns this node with `attributes` and `modifiers` prepended to the
  /// node’s attributes and modifiers, respectively. If the node doesn’t contain
  /// attributes or modifiers, `attributes` or `modifiers` are ignored and not
  /// applied.
  func applying(
    attributes: AttributeListSyntax?,
    modifiers: ModifierListSyntax?
  ) -> DeclSyntax {
    func _combine<C: SyntaxCollection>(_ left: C, _ right: C?) -> C? {
      guard let right = right else { return left }
      var elems: [C.Element] = []
      elems.append(contentsOf: left)
      elems.append(contentsOf: right)
      return C(elems)
    }
    var node = self
    if let attributes = attributes,
      let withAttrs = node.asProtocol(WithAttributesSyntax.self)
    {
      node = withAttrs.with(
        \.attributes,
        _combine(attributes, withAttrs.attributes)
      ).cast(DeclSyntax.self)
    }
    if let modifiers = modifiers,
      let withModifiers = node.asProtocol(WithModifiersSyntax.self)
    {
      node = withModifiers.with(
        \.modifiers,
        _combine(modifiers, withModifiers.modifiers)
      ).cast(DeclSyntax.self)
    }
    return node
  }
}

extension SyntaxProtocol {
  /// Expand all uses of the given set of macros within this syntax
  /// node.
  public func expand(
    macros: [String: Macro.Type],
    in context: some MacroExpansionContext
  ) -> Syntax {
    // Build the macro system.
    var system = MacroSystem()
    for (macroName, macroType) in macros {
      try! system.add(macroType, name: macroName)
    }

    let applier = MacroApplication(
      macroSystem: system,
      context: context
    )

    return applier.rewrite(self)
  }
}
