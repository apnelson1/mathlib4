/*
Copyright (c) 2022 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
*/
import * as React from 'react';

import { Position } from 'vscode-languageserver-protocol';
import { InteractiveCode, useAsync, RpcContext, CodeWithInfos, RpcSessionAtPos, DocumentPosition }
    from '@leanprover/infoview';

import commutativeDsl from './penrose/commutative.dsl';
import commutativeSty from './penrose/commutative.sty';
import commutativeSquareSub from './penrose/square.sub';
import commutativeTriangleSub from './penrose/triangle.sub';
import { PenroseCanvas } from './penrose';

type DiagramKind = 'square' | 'triangle'
interface DiagramData {
    objs: CodeWithInfos[]
    homs: CodeWithInfos[]
    kind: DiagramKind
}

function CommSquare({diag}: {diag: DiagramData}): JSX.Element {
    const [A,B,C,D] = diag.objs
    const [f,g,h,i] = diag.homs

    const mkElt = (fmt: CodeWithInfos): JSX.Element =>
        <div className="pa2">
            <InteractiveCode fmt={fmt} />
        </div>

    const embedNodes = new Map()
        .set("A", mkElt(A))
        .set("B", mkElt(B))
        .set("C", mkElt(C))
        .set("D", mkElt(D))
        .set("f", mkElt(f))
        .set("g", mkElt(g))
        .set("h", mkElt(h))
        .set("i", mkElt(i))

    return <PenroseCanvas
        trio={{dsl: commutativeDsl, sty: commutativeSty, sub: commutativeSquareSub}}
        embedNodes={embedNodes} maxOptSteps={500}
    />
}

function CommTriangle({diag}: {diag: DiagramData}): JSX.Element {
    const [A,B,C] = diag.objs
    const [f,g,h] = diag.homs

    const mkElt = (fmt: CodeWithInfos): JSX.Element =>
        <div className="pa2">
            <InteractiveCode fmt={fmt} />
        </div>

    const embedNodes = new Map()
        .set("A", mkElt(A))
        .set("B", mkElt(B))
        .set("C", mkElt(C))
        .set("f", mkElt(f))
        .set("g", mkElt(g))
        .set("h", mkElt(h))

    return <PenroseCanvas
        trio={{dsl: commutativeDsl, sty: commutativeSty, sub: commutativeTriangleSub}}
        embedNodes={embedNodes} maxOptSteps={500}
    />
}

async function getCommutativeDiagram(rs: RpcSessionAtPos, pos: Position)
        : Promise<DiagramData | undefined> {
    return rs.call<Position, DiagramData | undefined>('getCommutativeDiagram', pos)
}

export default function({pos}: {pos: DocumentPosition}): React.ReactNode {
    const rs = React.useContext(RpcContext)
    const res = useAsync(() => getCommutativeDiagram(rs, pos), [rs, pos])
    // Store the diagram data in state so that even when a new diagram is loading,
    // we still temporarily show the present one. This reduces flickering.
    const [diag, setDiag] = React.useState<DiagramData | undefined>(undefined)

    React.useEffect(() => {
        if (res.state === 'rejected' ||
            (res.state === 'resolved' && !res.value))
            setDiag(undefined)
        else if (res.state === 'resolved')
            setDiag(res.value)
    }, [res.state])

    let msg = <></>
    if (res.state === 'loading')
        msg = <>Loading diagram..</>
    else if (res.state === 'rejected')
        msg = <>Error: {JSON.stringify(res.error)}</>
    else if (res.state === 'resolved' && !res.value)
        msg = <>Error: no diagram.</>

    return <>
        {diag && diag.kind === 'square' &&
            <CommSquare diag={diag} />}
        {diag && diag.kind === 'triangle' &&
            <CommTriangle diag={diag} />}
        {msg}
    </>
}
