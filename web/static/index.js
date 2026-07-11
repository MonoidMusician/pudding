import { Stream } from "./js/Riverdragon.js";

const { _, ById, HTML } = Verity;

const tab = Stream.createStore("elab");
const input = Stream.createStore({ input: "", filename: "" });
const output = Stream.createStore([]);
const outputTab = Stream.combineStreams(
    [_=>true, _=>true],
    (output, tab) => ({ output, tab }),
    output.stream, tab.stream,
);
const tabOutput = Stream.createStore({ className: "", html: "" });
const section = Stream.createStore("compose");

const tab_container = ById.output_side.querySelector(".tabs");
const tab_by_name = Object.fromEntries([
    ...tab_container.querySelectorAll("button")
].map(b => [b.textContent, b]));


outputTab.subscribe(v => {
    for (const [name, stage] of v.output) {
        const tab = tab_by_name[name];
        if (stage.stageError) {
            tab.classList.add("error");
        } else {
            tab.classList.remove("error");
        }
    }
    for (const [name, stage] of v.output) {
        if (name === v.tab || stage.stageError) {
            if (stage.stageError) {
                const prefix = {
                    parse: "Parse error at ",
                }[name] ?? "";
                tabOutput.send({ html: prefix + stage.stageError.html, className: "error" })
            } else {
                tabOutput.send({ html: stage.stageContent.html, className: "" });
            }
            if (name === v.tab)
                break;
        }
    }
});

const actions = {
    file_load() {
        const filename = ById.filename.value;
        if (!filename) return;
        Ve.POST("/api/surface/load", filename).then(content => {
            ById.input.value = content;
            actions.update();
        });
    },
    async update() {
        const r = await Ve.POST("/api/surface/test", {
            content: ById.input.value,
            filename: ById.filename.value || undefined,
        });
        console.log(r);
        output.send(r);
    },
    async refresh_files() {
        Ve.GET("/api/surface/list").then(items => {
            console.log(items);
            /** @type HTMLSelectElement */
            const sel = ById.file_select;
            let val = sel.value;
            for (const child of [...sel.children].slice(1)) {
                child.removeSelf();
            }
            for (const item of items) {
                sel.appendChild(HTML.option([item]));
                if (item === ById.filename.value)
                    val = ById.filename.value;
            }
            sel.value = val;
            sel.value = sel.value; // default it to ""
        });
    },
    async section_compose() {
        await actions.refresh_files();
    },
    async board_refresh() {
        /** @type HTMLDivElement */
        const dash = ById.results;
        dash.replaceChildren();
        const results = await Ve.GET("/api/surface/report");
        for (const [name, [content, success, stages]] of results) {
            dash.appendChild(HTML.tr({
                class: success ? 'succeeded' : 'failed',
            }, [
                HTML.th(name),
                HTML.td(success ? "succeeded" : "failed"),
            ]));
        }
    },
    async section_dashboard() {
        await actions.board_refresh();
    },
};

Verity.ContentLoad(() => {
    section.send(document.querySelector("input[name=section_tab]:checked")?.value ?? section.current());
    Ve.forQuery("input[name=section_tab]", which => {
        Ve.on.change(which, () => {
            console.log(which);
            if (which.checked)
                section.send(which.value);
        });
    });
    section.stream.subscribe(current => {
        const section_current = `section_${current}`;
        Ve.forQuery("section", section => {
            const selected = section.id === section_current;
            console.log(selected, section);
            section.style.display = selected ? null : "none";
        });
        actions[section_current]?.();
    });

    Ve.on.click(ById.board_refresh, () => {
        actions.section_dashboard();
    });
});

Verity.ContentLoad(() => {
    input.send(ById.input.value);

    for (const char of ById.compose_chars.querySelectorAll("button")) {
        Ve.on.click(char, () => {
            const c = char.textContent;
            /** @type HTMLInputElement */
            const t = ById.input;
            const { value: v, selectionStart: s, selectionEnd: e } = t;

            // Replace the selection with the character
            Object.assign(t, {
                value: v.substring(0, s) + c + v.substring(e),
                selectionStart: s + c.length,
                selectionEnd: s + c.length,
            });
            // And refocus for more keyboard input
            t.focus();
            // And update
            actions.update();
        });
    }

    Ve.on.input(ById.input, actions.update);
    Ve.on.input(ById.filename, () => {
        const val = ById.filename.value;
        for (const child of [...ById.file_select].slice(1)) {
            if (child.value === val) {
                ById.file_select.value = val;
                return;
            }
        }
        ById.file_select.value = ById.file_select.firstElementChild.value;
    });

    Ve.on.click(tab_container, (e) => {
        if (e.target instanceof HTMLButtonElement) {
            const selected = e.target.textContent;
            tab.send(selected);
        }
    });

    tab.stream.subscribe(selected => {
        for (const tab of tab_container.querySelectorAll("button")) {
            if (tab.textContent === selected) {
                tab.classList.add("selected");
            } else {
                tab.classList.remove("selected");
            }
        }
    });

    tabOutput.stream.subscribe(o => {
        ById.output.innerHTML = o.html;
        ById.output.className = o.className;
    });

    actions.refresh_files();
    Ve.on.click(ById.file_refresh, actions.refresh_files);

    Ve.on.input(ById.file_select, ({ target }) => {
        if (target.options.selectedIndex > 0) {
            ById.filename.value = target.value;
            actions.file_load();
        }
    });

    Ve.on.click(ById.file_load, actions.file_load);

    Ve.on.click(ById.file_save, () => {
        const filename = ById.filename.value;
        if (!filename) return;
        const selection = [];
        Ve.forQuery("#output_side .tabs > .tab > .formats input[type=checkbox]", e => {
            if (e.checked) selection.push(e.value);
        });
        Ve.POST("/api/surface/save", { filename, content: ById.input.value, extra: selection }).then(actions.refresh_files);
    });

    Ve.on.click(ById.file_delete, () => {
        const filename = ById.filename.value;
        if (!filename) return;
        Ve.POST("/api/surface/save", { filename, content: "" }).then(actions.refresh_files);
    });
});
