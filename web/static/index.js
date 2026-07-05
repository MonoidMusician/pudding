
const { _, ById, HTML } = Verity;

const update = async () => {
    const r = await Ve.POST("/api/parse/surface", {
        content: ById.input.value,
        filename: ById.filename.value || undefined,
    });
    console.log(r);
    for (const [name, stage] of r) {
        if (stage.stageError) {
            ById.output.innerHTML = stage.stageError.html;
        } else {
            ById.output.innerHTML = stage.stageContent.html;
        }
    }
};

Verity.ContentLoad(() => {
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
            update();
        });
    }

    Ve.on.input(ById.input, update);
});
