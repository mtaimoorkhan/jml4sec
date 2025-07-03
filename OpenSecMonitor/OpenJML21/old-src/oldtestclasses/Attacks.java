package uk.gre.ac.openjmlsec.testclasses;

public enum Attacks {
    SQL_OR_ATTACK(1), SQL_AND_ATTACK(2), INJECTION(3), NONE(0), TEST(-1);

    private final int attack;

    private Attacks(int attack) {
        this.attack = attack;
    }

    public boolean isAttack() {
        return this.attack != 0;
    }
}
